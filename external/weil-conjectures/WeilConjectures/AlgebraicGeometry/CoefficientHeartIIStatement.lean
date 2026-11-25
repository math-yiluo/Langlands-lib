/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Data.Fin.Tuple.Basic
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStatement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedCohomologyConeWitness
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Triangulation and finite cone generation for field coefficients

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-cor-coefficient-heart-ii/_section.md`
and `sk-cor-coefficient-heart-ii.proof.md` (blueprint: corollary-coefficient-heart-b).

The standing setting is a separated finite-type scheme over a field of positive
characteristic, with characteristic different from the coefficient prime.  The
constructible property is the existing bounded constructible property for the
pulled-back condensed coefficient ring.  The proof follows the blueprint: the long
exact cohomology sequence with the closure clause of `lemma-constructible-sheaves`,
then truncation induction and the finite filtration clause of that lemma.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private def heartIIValid {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    {n : ℕ} (F : Fin n → C) : Prop :=
  ∀ r, G (F r) ∨ ∃ i j, i < r ∧ j < r ∧ R (F i) (F j) (F r)

private def heartIIWitness {C : Type*} (G : C → Prop) (R : C → C → C → Prop)
    (K : C) : Prop :=
  ∃ (N : ℕ) (F : Fin (N + 1) → C), F (Fin.last N) = K ∧ heartIIValid G R F

private theorem heartIIValid_append {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {m n : ℕ} {F : Fin m → C} {H : Fin n → C}
    (hF : heartIIValid G R F) (hH : heartIIValid G R H) :
    heartIIValid G R (Fin.append F H) := by
  intro r
  refine Fin.addCases (fun r ↦ ?_) (fun r ↦ ?_) r
  · rcases hF r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.castAdd n, j.castAdd n, ?_, ?_, ?_⟩
      · exact hi
      · exact hj
      · simpa using h
  · rcases hH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · right
      refine ⟨i.natAdd m, j.natAdd m, ?_, ?_, ?_⟩
      · simpa using hi
      · simpa using hj
      · simpa using h

private theorem heartIIWitness_generator {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {K : C} (hK : G K) : heartIIWitness G R K := by
  exact ⟨0, fun _ ↦ K, rfl, fun _ ↦ Or.inl hK⟩

private theorem heartIIWitness_step {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {A B K : C}
    (hA : heartIIWitness G R A) (hB : heartIIWitness G R B)
    (hK : R A B K) : heartIIWitness G R K := by
  obtain ⟨m, F, hF, hvF⟩ := hA
  obtain ⟨n, H, hH, hvH⟩ := hB
  refine ⟨(m + 1) + (n + 1), Fin.snoc (Fin.append F H) K, by simp, ?_⟩
  intro r
  refine Fin.lastCases ?_ (fun r ↦ ?_) r
  · right
    refine ⟨((Fin.last m).castAdd (n + 1)).castSucc,
      ((Fin.last n).natAdd (m + 1)).castSucc, ?_, ?_, ?_⟩
    · exact Fin.castSucc_lt_last _
    · exact Fin.castSucc_lt_last _
    · simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.append_left,
        Fin.append_right, hF, hH] using hK
  · rcases heartIIValid_append hvF hvH r with h | ⟨i, j, hi, hj, h⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨i.castSucc, j.castSucc, hi, hj, by simpa using h⟩

private def heartIICone {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (U V W : DerivedCategory A) : Prop :=
  ∃ (n : ℤ) (f : U ⟶ V) (g : V ⟶ W⟦n⟧) (h : W⟦n⟧ ⟶ U⟦(1 : ℤ)⟧),
    Pretriangulated.Triangle.mk f g h ∈ distTriang _

private theorem heartIIWitness_triangle {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (G : DerivedCategory A → Prop)
    (T : Pretriangulated.Triangle (DerivedCategory A)) (hT : T ∈ distTriang _)
    (h₁ : heartIIWitness G (heartIICone (A := A)) T.obj₁)
    (h₂ : heartIIWitness G (heartIICone (A := A)) T.obj₂) :
    heartIIWitness G (heartIICone (A := A)) T.obj₃ := by
  apply heartIIWitness_step h₁ h₂
  let e := (shiftFunctorZero (DerivedCategory A) ℤ).app T.obj₃
  refine ⟨0, T.mor₁, T.mor₂ ≫ e.inv, e.hom ≫ T.mor₃, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT
  exact Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp)

private theorem heartIIWitness_filtration {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (G : DerivedCategory A → Prop) (m : ℕ)
    (B : Fin (m + 1) → A) (f : ∀ a : Fin m, B a.castSucc ⟶ B a.succ)
    (hf : ∀ a, Mono (f a)) (n : ℤ) (hz : IsZero (B 0))
    (hzero : ∀ Z : DerivedCategory A, IsZero Z → heartIIWitness G (heartIICone (A := A)) Z)
    (hg : ∀ a, G ((((DerivedCategory.singleFunctor A 0).obj (cokernel (f a)))⟦n⟧)
      ⟦(-1 : ℤ)⟧)) :
    heartIIWitness G (heartIICone (A := A))
      (((DerivedCategory.singleFunctor A 0).obj (B (Fin.last m)))⟦n⟧) := by
  have tower (k : ℕ) (hk : k < m + 1) :
      heartIIWitness G (heartIICone (A := A))
        (((DerivedCategory.singleFunctor A 0).obj (B ⟨k, hk⟩))⟦n⟧) := by
    induction k with
    | zero =>
      exact hzero _ ((shiftFunctor _ n).map_isZero
        ((DerivedCategory.singleFunctor A 0).map_isZero hz))
    | succ k ih =>
      let a : Fin m := ⟨k, by omega⟩
      have : Mono (f a) := hf a
      let S := ShortComplex.mk (f a) (cokernel.π (f a)) (cokernel.condition (f a))
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (f a))
          inferInstance inferInstance
      let T := (shiftFunctor (Pretriangulated.Triangle (DerivedCategory A)) n).obj
        hS.singleTriangle
      have hT : T ∈ distTriang _ :=
        Pretriangulated.Triangle.shift_distinguished _ hS.singleTriangle_distinguished n
      exact heartIIWitness_triangle G T.invRotate
        (Pretriangulated.inv_rot_of_distTriang T hT)
        (heartIIWitness_generator (hg a)) (ih (by omega))
  exact tower m (Nat.lt_succ_self _)

private theorem heartIIWitness_iso {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory A] (G : DerivedCategory A → Prop)
    (hzero : ∀ Z : DerivedCategory A, IsZero Z →
      heartIIWitness G (heartIICone (A := A)) Z)
    {U V : DerivedCategory A} (e : U ≅ V)
    (hU : heartIIWitness G (heartIICone (A := A)) U) :
    heartIIWitness G (heartIICone (A := A)) V := by
  let T := Pretriangulated.Triangle.mk (0 : 0 ⟶ U) e.hom 0
  have hT : T ∈ distTriang _ := by
    apply Pretriangulated.isomorphic_distinguished _
      (Pretriangulated.contractible_distinguished₁ U)
    exact Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
      (by simp [T]) (by change e.hom ≫ e.inv = 𝟙 U ≫ 𝟙 U; simp) (by simp [T])
  exact heartIIWitness_triangle G T hT (hzero _ (isZero_zero _)) hU

private theorem heartIIWitness_subobject_filtration {A : Type w}
    [Category.{v} A] [Abelian A] [HasDerivedCategory A]
    (G : DerivedCategory A → Prop) (M : A) (m : ℕ)
    (B : Fin (m + 1) → Subobject M) (hb : B 0 = ⊥) (ht : B (Fin.last m) = ⊤)
    (hle : ∀ a : Fin m, B a.castSucc ≤ B a.succ) (n : ℤ)
    (hzero : ∀ Z : DerivedCategory A, IsZero Z →
      heartIIWitness G (heartIICone (A := A)) Z)
    (hg : ∀ a : Fin m, G
      ((((DerivedCategory.singleFunctor A 0).obj
        (cokernel (Subobject.ofLE (B a.castSucc) (B a.succ) (hle a))))⟦n⟧)⟦(-1 : ℤ)⟧)) :
    heartIIWitness G (heartIICone (A := A))
      (((DerivedCategory.singleFunctor A 0).obj M)⟦n⟧) := by
  have hz : IsZero (B 0 : A) :=
    (isZero_zero A).of_iso (Subobject.isoOfEq _ _ hb ≪≫ Subobject.botCoeIsoZero)
  have hw := heartIIWitness_filtration G m (fun k ↦ (B k : A))
    (fun a ↦ Subobject.ofLE _ _ (hle a)) (fun a ↦ inferInstance) n hz hzero hg
  have e : (B (Fin.last m) : A) ≅ M :=
    Subobject.isoOfEq _ _ ht ≪≫ Subobject.underlyingIso (𝟙 M)
  exact heartIIWitness_iso G hzero
    ((shiftFunctor _ n).mapIso ((DerivedCategory.singleFunctor A 0).mapIso e)) hw

private theorem heartIIWitness_induction {C : Type*} {G : C → Prop}
    {R : C → C → C → Prop} {P : C → Prop}
    (hG : ∀ K, G K → P K)
    (hR : ∀ A B K, R A B K → P A → P B → P K)
    {K : C} (hK : heartIIWitness G R K) : P K := by
  obtain ⟨N, F, hF, hv⟩ := hK
  have h : ∀ n (hn : n < N + 1), P (F ⟨n, hn⟩) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases hv ⟨n, hn⟩ with h | ⟨i, j, hi, hj, h⟩
      · exact hG _ h
      · exact hR _ _ _ h (ih i.val hi i.isLt) (ih j.val hj j.isLt)
  rw [← hF]
  exact h N (Nat.lt_succ_self N)

private theorem heartIIWitness_bind {C : Type*} {G H : C → Prop}
    {R : C → C → C → Prop} {K : C} (hK : heartIIWitness G R K)
    (hG : ∀ A, G A → heartIIWitness H R A) : heartIIWitness H R K := by
  exact heartIIWitness_induction hG
    (fun _ _ _ h hA hB ↦ heartIIWitness_step hA hB h) hK

private theorem heartIIExtension_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) (ha : IsImmersion a) :
    IsZero ((coefficientHeartLocallyClosedExtension Λ a ha).obj 0) := by
  let : IsImmersion a := ha
  let : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  exact (CondensedRing.lowerStar Λ a.imageι).map_isZero
    ((CondensedRing.openImmersionLowerShriek Λ a.toImage).map_isZero (isZero_zero _))

/-- In the standing coefficient setting, bounded constructible complexes form a
triangulated subcategory and admit finite cone presentations by shifted locally
closed extensions of lisse modules.

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-cor-coefficient-heart-ii/_section.md`
and `sk-cor-coefficient-heart-ii.proof.md`, both paragraphs
(blueprint: corollary-coefficient-heart-b).

The first conjunct is the triangulated-subcategory assertion.  The second
conjunct gives a finite sequence ending at the chosen complex; each term is
an integer shift of a canonical locally closed extension of a lisse module,
or is a shifted cone whose two inputs occur earlier in the sequence.  The
Noetherian structure used by the canonical extension is constructed from the
standing finite-type and quasi-compact hypotheses.

Proof plan, following the node's three steps:
1. For a distinguished triangle `K → K' → K'' → K[1]` with `K, K'` bounded
   constructible, the long exact homology sequence
   (lem-sf-derived-homology-long-exact) makes each `H^i K''` an extension of
   `ker(H^{i+1} K → H^{i+1} K')` by `coker(H^i K → H^i K')`; both are constructible by
   clause (1) of lemma-constructible-sheaves, hence so is `H^i K''`, and `K''` vanishes
   outside `[a-1, b]` when `K, K'` live in `[a, b]`.  Zero and isomorphic objects stay
   inside, `H^i(K[n]) = H^{i+n}(K)` gives shift stability, and rotation gives
   two-out-of-three: the property is triangulated.
2. Generation: induct on the number of nonzero `H^i K`.  If none, `K ≅ 0`, the cone of
   the identity of `Λ_X[0]` (`a = id_X`, free rank-one lisse module).  Otherwise let
   `i` be the top degree; the truncation triangle
   (def-sbc-standard-tstructure-derived-category, theorem-pbc-injective-acyclicity)
   `τ_{<i} K → K → H^i(K)[-i] →` rotated backwards exhibits `K` as a cone of
   `H^i(K)[-i-1] → τ_{<i} K`, and `τ_{<i} K` has one fewer nonzero cohomology sheaf.
3. For a constructible sheaf `F`, the filtration of clause (3) of
   lemma-constructible-sheaves has quotients `a_{k!} L_k`; each short exact sequence
   `0 → F_{k-1} → F_k → a_{k!} L_k → 0` is a distinguished triangle
   (lem-sf-derived-ses-triangle), so backward rotation builds `F` (and all its shifts)
   by finitely many cones from shifted generators.  Concatenating these finite
   sequences with the cones of step 2 gives the finite sequence of the conclusion.
-/
theorem coefficientHeartIIStatement (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (constantModelBoundedConstructible (coefficientHeartRingObj Λ) X).IsTriangulated ∧
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) X)),
        constantModelBoundedConstructible (coefficientHeartRingObj Λ) X K →
          ∃ (N : ℕ) (F : Fin (N + 1) → DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
              (condensedRingObj (coefficientHeartRingObj Λ) X))),
            F (Fin.last N) = K ∧ ∀ r : Fin (N + 1),
              (∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
                (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
                  (condensedRingObj (coefficientHeartRingObj Λ) S)) (n : ℤ),
                IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
                  Nonempty (F r ≅ ((DerivedCategory.singleFunctor _ 0).obj
                    ((@coefficientHeartLocallyClosedExtension
                      (coefficientHeartRingObj Λ) _ S X
                      (@AlgebraicGeometry.IsNoetherian.noetherianSpace X
                        { toIsLocallyNoetherian :=
                            LocallyOfFiniteType.isLocallyNoetherian
                              (X ↘ Spec (.of k))
                          toCompactSpace :=
                            QuasiCompact.compactSpace_of_compactSpace
                              (X ↘ Spec (.of k)) }) a ha).obj L))⟦n⟧)) ∨
              (∃ (i j : Fin (N + 1)), i < r ∧ j < r ∧
                ∃ (n : ℤ) (f : F i ⟶ F j) (g : F j ⟶ (F r)⟦n⟧)
                  (h : (F r)⟦n⟧ ⟶ (F i)⟦(1 : ℤ)⟧),
                  Pretriangulated.Triangle.mk f g h ∈ distTriang _) := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace :=
        QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have hheart := coefficientHeartStatement ℓ Λ hΛ k p hpℓ X
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (coefficientHeartRingObj Λ) X)
  let P : ObjectProperty A := IsConstantModelConstructible (coefficientHeartRingObj Λ) X
  have : P.IsClosedUnderKernels := hheart.1
  have : P.IsClosedUnderCokernels := hheart.2.1
  have : P.IsClosedUnderExtensions := hheart.2.2.1
  have : Abelian P.FullSubcategory := hheart.2.2.2.1.some
  have : PreservesFiniteLimits P.ι := hheart.2.2.2.2.1
  have : P.IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined (coefficientHeartRingObj Λ) X).1
  have : P.ContainsZero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := P.FullSubcategory)
    exact ⟨⟨Z.obj, P.ι.map_isZero hZ, Z.property⟩⟩
  constructor
  · change (DerivedCategory.TStructure.t.bounded ⊓
      DerivedCategory.homologyProperty P).IsTriangulated
    infer_instance
  · intro K hK
    let D := DerivedCategory A
    let G : D → Prop := fun W ↦
      ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
        (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) S)) (n : ℤ),
        IsLisseCoefficientModule (coefficientHeartRingObj Λ) L ∧
          Nonempty (W ≅ ((DerivedCategory.singleFunctor A 0).obj
            ((coefficientHeartLocallyClosedExtension
              (coefficientHeartRingObj Λ) a ha).obj L))⟦n⟧)
    let R : D → D → D → Prop := heartIICone (A := A)
    change heartIIWitness G R K
    -- Rank zero supplies a generator for every zero object, including the empty scheme.
    have hzL : IsLisseCoefficientModule (coefficientHeartRingObj Λ) (0 : A) := by
      refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 X)
        (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
      refine ⟨0, ⟨?_⟩⟩
      apply IsZero.iso
      · exact (CondensedRing.upperStar (coefficientHeartRingObj Λ) _).map_isZero
          (isZero_zero _)
      · rw [IsZero.iff_id_eq_zero]
        apply biproduct.hom_ext
        intro j
        exact Fin.elim0 j
    have hzExt : IsZero
        ((coefficientHeartLocallyClosedExtension (coefficientHeartRingObj Λ) (𝟙 X)
          inferInstance).obj (0 : A)) :=
      heartIIExtension_zero (coefficientHeartRingObj Λ) (𝟙 X) inferInstance
    have hzero (Z : D) (hz : IsZero Z) : heartIIWitness G R Z := by
      apply heartIIWitness_generator
      refine ⟨X, 𝟙 X, inferInstance, 0, 0, hzL, ⟨?_⟩⟩
      exact hz.iso ((shiftFunctor D (0 : ℤ)).map_isZero
        ((DerivedCategory.singleFunctor A 0).map_isZero hzExt))
    -- Apply clause (3) of the heart theorem to each cohomology sheaf, then turn
    -- its successive cokernel sequences into inverse-rotated single triangles.
    have sheaf_witness (M : A) (hM : P M) (n : ℤ) (W : D)
        (hW : Nonempty (W ≅ ((DerivedCategory.singleFunctor A 0).obj M)⟦n⟧)) :
        heartIIWitness G R W := by
      obtain ⟨m, B, hbot, htop, hle, hquot⟩ :=
        hheart.2.2.2.2.2.2.2 ⟨M, hM⟩
      have tower : heartIIWitness G R
          (((DerivedCategory.singleFunctor A 0).obj M)⟦n⟧) := by
        apply heartIIWitness_subobject_filtration G M m B hbot htop hle n hzero
        intro a
        obtain ⟨S, j, hj, L, hL, ⟨e⟩⟩ := hquot a
        refine ⟨S, j, hj, L, n + -1, hL, ⟨?_⟩⟩
        exact (shiftFunctor D (-1 : ℤ)).mapIso
            ((shiftFunctor D n).mapIso ((DerivedCategory.singleFunctor A 0).mapIso e)) ≪≫
          (shiftFunctorAdd D n (-1 : ℤ)).symm.app _
      obtain ⟨eW⟩ := hW
      exact heartIIWitness_iso G hzero eW.symm tower
    -- The generic truncation induction gives leaves H^q(K)[n]. Substitution
    -- concatenates their finite filtrations and appends each required cone.
    have hw := DerivedCategory.bounded_cohomology_cone_witness A K hK.1
    let H : D → Prop := fun W ↦ ∃ q n : ℤ,
      Nonempty (W ≅ ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A q).obj K))⟦n⟧)
    have hw' : heartIIWitness H R K := hw
    apply heartIIWitness_bind hw'
    rintro W ⟨q, n, hW⟩
    exact sheaf_witness _ (hK.2 q) n W hW

end AlgebraicGeometry.ProEtale
