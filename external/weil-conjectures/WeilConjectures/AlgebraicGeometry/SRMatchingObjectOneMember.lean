/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
import WeilConjectures.AlgebraicGeometry.SemiRepresentableCoveringPermanence
import WeilConjectures.CategoryTheory.SimplicialMatchingObject
import all WeilConjectures.AlgebraicGeometry.HypercoverOneMoreSimplex
import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Matching schemes and one-member semi-representable families

Source: Stacks Project, Hypercoverings, Tags 01G2, 01G3, 01G5; Simplicial Methods,
Tag 0186 (auxiliary; not a blueprint node).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def inclLimit {C : Type*} [Category* C]
    {J : Type*} [Category* J] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) :
    IsLimit ((FormalCoproduct.incl.{w} C).mapCone c) := by
  let d (s : Cone (F ⋙ FormalCoproduct.incl.{w} C)) (i : s.pt.I) : Cone F :=
    { pt := s.pt.obj i
      π := { app := fun a ↦ (s.π.app a).φ i
             naturality := fun a b f ↦ by
               have h := congrArg
                 (fun g : s.pt ⟶ (FormalCoproduct.incl C).obj (F.obj b) ↦
                   (show s.pt.obj i ⟶ F.obj b from g.φ i)) (s.w f)
               simpa [Functor.mapCone, FormalCoproduct.incl] using h.symm } }
  refine { lift := fun s ↦ ⟨fun _ ↦ PUnit.unit, fun i ↦ hc.lift (d s i)⟩
           fac := ?_
           uniq := ?_ }
  · intro s a
    apply FormalCoproduct.hom_ext (by rfl)
    intro i
    simp [Functor.mapCone, FormalCoproduct.incl, d]
  · intro s m hm
    apply FormalCoproduct.hom_ext (by funext i; exact Subsingleton.elim (α := PUnit) _ _)
    intro i
    apply hc.hom_ext
    intro a
    have h := congrArg
      (fun g : s.pt ⟶ (FormalCoproduct.incl C).obj (F.obj a) ↦
        (show s.pt.obj i ⟶ F.obj a from g.φ i)) (hm a)
    simpa [Functor.mapCone, FormalCoproduct.incl] using h
private theorem etaleFaces (X : Scheme.{u}) (U : SimplicialObject X.Etale) (n : ℕ) :
    ∃ (c : Cone (U.properFaceDiagram n)) (μ : U _⦋n⦌ ⟶ c.pt),
      (n = 0 → c.pt = Etale.mk (𝟙 X)) ∧ Nonempty (IsLimit c) ∧
      (∀ a : SimplicialObject.ProperFaceCategory n,
        μ ≫ c.π.app (op a) = U.map a.obj.hom.op) := by
  classical
  rcases n with _ | _ | n
  · let T := Etale.mk (𝟙 X)
    have ht : IsTerminal T :=
      Over.mkIdTerminal.isTerminalOfObj (Etale.forget X) T
    let c : Cone (U.properFaceDiagram 0) :=
      ⟨T, { app := fun a ↦ (Nat.not_lt_zero _ a.unop.property.1).elim
            naturality := fun a b f ↦ (Nat.not_lt_zero _ a.unop.property.1).elim }⟩
    refine ⟨c, ht.from _, fun _ ↦ rfl, ⟨?_⟩, ?_⟩
    · exact { lift := fun s ↦ ht.from s.pt
              fac := fun s a ↦ (Nat.not_lt_zero _ a.unop.property.1).elim
              uniq := fun s m hm ↦ ht.hom_ext _ _ }
    · intro a
      exact (Nat.not_lt_zero _ a.property.1).elim
  · let c : Fan (fun _ : Fin 2 ↦ U _⦋0⦌) :=
      limit.cone (Discrete.functor (fun _ : Fin 2 ↦ U _⦋0⦌))
    have hc : Nonempty (IsLimit c) := ⟨limit.isLimit _⟩
    let μ : U _⦋1⦌ ⟶ c.pt := Fan.IsLimit.lift hc.some (fun i ↦ U.δ i)
    have hμ : ∀ i : Fin 2, μ ≫ c.proj i = U.δ i :=
      fun i ↦ Fan.IsLimit.fac hc.some _ i
    obtain ⟨π, hπ, _, hfac, _⟩ :=
      (SimplicialObject.matching_object_proper_faces_one U c hc.some μ hμ).2
    exact ⟨Cone.mk c.pt π, μ, by omega, hπ, hfac⟩
  · let : Fintype (SimplicialObject.matchingBoundaryShape n).L :=
      inferInstanceAs (Fintype (Fin (n + 3)))
    let : Fintype (SimplicialObject.matchingBoundaryShape n).R :=
      inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
    let : DecidableEq (SimplicialObject.matchingBoundaryShape n).L :=
      inferInstanceAs (DecidableEq (Fin (n + 3)))
    let : DecidableEq (SimplicialObject.matchingBoundaryShape n).R :=
      inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
    let c : Multifork (SimplicialObject.matchingBoundaryIndex U n) :=
      Multiequalizer.multifork _
    have hc : Nonempty (IsLimit c) := ⟨limit.isLimit _⟩
    have hδ : ∀ p : (SimplicialObject.matchingBoundaryShape n).R,
        U.δ p.val.1 ≫ (SimplicialObject.matchingBoundaryIndex U n).fst p =
          U.δ p.val.2 ≫ (SimplicialObject.matchingBoundaryIndex U n).snd p := by
      rintro ⟨⟨a, b⟩, h⟩
      dsimp [SimplicialObject.matchingBoundaryIndex]
      have hb : b = (b.pred (Fin.ne_zero_of_lt h)).succ := (Fin.succ_pred _ _).symm
      have H : a.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ b.isLt)) ≤
          b.pred (Fin.ne_zero_of_lt h) := by
        rw [Fin.le_iff_val_le_val]
        have h' : a.val < b.val := h
        simp only [Fin.val_castLT, Fin.val_pred]
        omega
      have hface := (SimplicialObject.δ_comp_δ U H).symm
      rw [← hb] at hface
      exact hface
    let μ : U _⦋n + 2⦌ ⟶ c.pt :=
      Multifork.IsLimit.lift hc.some (fun i ↦ U.δ i) hδ
    have hμ : ∀ i : Fin (n + 3),
        μ ≫ c.π.app (WalkingMulticospan.left i) = U.δ i :=
      fun i ↦ Multifork.IsLimit.fac hc.some _ hδ i
    obtain ⟨π, hπ, _, hfac, _⟩ :=
      (SimplicialObject.matching_object_proper_faces_succ_succ U n c hc.some μ hμ).2
    exact ⟨Cone.mk c.pt π, μ, by omega, hπ, hfac⟩

private theorem srFaces (X : Scheme.{u})
    (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ) :
    ∃ π : (Functor.const _).obj (semiRepresentableMatchingObject K n) ⟶
        K.properFaceDiagram n,
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      (∀ a : SimplicialObject.ProperFaceCategory n,
        semiRepresentableMatchingMap K n ≫ π.app (op a) = K.map a.obj.hom.op) := by
  classical
  rcases n with _ | _ | n
  · let T := Etale.mk (𝟙 X)
    have ht : IsTerminal ((FormalCoproduct.incl X.Etale).obj T) :=
      FormalCoproduct.isTerminalIncl _
        (Over.mkIdTerminal.isTerminalOfObj (Etale.forget X) T)
    let π : (Functor.const _).obj (semiRepresentableMatchingObject K 0) ⟶
        K.properFaceDiagram 0 :=
      { app := fun a ↦ (Nat.not_lt_zero _ a.unop.property.1).elim
        naturality := fun a b f ↦ (Nat.not_lt_zero _ a.unop.property.1).elim }
    refine ⟨π, ⟨?_⟩, fun a ↦ (Nat.not_lt_zero _ a.property.1).elim⟩
    exact { lift := fun s ↦ ht.from s.pt
            fac := fun s a ↦ (Nat.not_lt_zero _ a.unop.property.1).elim
            uniq := fun s m hm ↦ ht.hom_ext _ _ }
  · let c : Fan (fun _ : Fin 2 ↦ K _⦋0⦌) := limit.cone (Discrete.functor (fun _ : Fin 2 ↦ K _⦋0⦌))
    have hμ : ∀ i : Fin 2, semiRepresentableMatchingMap K 1 ≫ c.proj i = K.δ i := by
      intro i
      change (Pi.lift fun i ↦ K.δ i) ≫ Pi.π _ i = _
      simp
    obtain ⟨π, hπ, _, hfac, _⟩ :=
      (SimplicialObject.matching_object_proper_faces_one K c (limit.isLimit _)
        (semiRepresentableMatchingMap K 1) hμ).2
    exact ⟨π, hπ, hfac⟩
  · let c : Cone (SimplicialObject.matchingBoundaryIndex K n).multicospan :=
      Multiequalizer.multifork _
    have hμ : ∀ i : Fin (n + 3), semiRepresentableMatchingMap K (n + 2) ≫
        c.π.app (WalkingMulticospan.left i) = K.δ i := by
      intro i
      simp [semiRepresentableMatchingMap, c]
    obtain ⟨π, hπ, _, hfac, _⟩ :=
      (SimplicialObject.matching_object_proper_faces_succ_succ K n c (limit.isLimit _)
        (semiRepresentableMatchingMap K (n + 2)) hμ).2
    exact ⟨π, hπ, hfac⟩
private theorem properFace_finite (n : ℕ) :
    Finite (SimplicialObject.ProperFaceCategory n) := by
  let f (a : SimplicialObject.ProperFaceCategory n) :
      Σ r : Fin n, (SimplexCategory.mk r.val ⟶ SimplexCategory.mk n) :=
    ⟨⟨a.obj.left.len, a.property.1⟩, a.obj.hom⟩
  apply Finite.of_injective f
  rintro ⟨⟨a, ar, ah⟩, ha⟩ ⟨⟨b, br, bh⟩, hb⟩ h
  have hab : a = b := SimplexCategory.ext (congrArg (fun x ↦ x.1.val) h)
  subst b
  cases ar
  cases br
  have hr : ah = bh := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst bh
  rfl

@[instance_reducible] private noncomputable def properFace_finCategory (n : ℕ) :
    FinCategory (SimplicialObject.ProperFaceCategory n) where
  fintypeObj := @Fintype.ofFinite _ (properFace_finite n)
  fintypeHom a b := by
    have : Finite (a.obj.left ⟶ b.obj.left) := inferInstance
    have : Finite (a ⟶ b) := Finite.of_injective (fun f ↦ f.hom.left) (by
      intro f g h
      apply ObjectProperty.hom_ext
      exact Over.OverMorphism.ext h)
    exact Fintype.ofFinite _

private theorem geometry (X : Scheme.{u}) (U : SimplicialObject X.Etale) :
    ∃ (M : ℕ → X.Etale)
      (π : ∀ n : ℕ, (Functor.const _).obj (M n) ⟶ U.properFaceDiagram n)
      (μ : ∀ n : ℕ, U _⦋n⦌ ⟶ M n),
      M 0 = Etale.mk (𝟙 X) ∧
      (∀ n : ℕ,
        Nonempty (IsLimit ((Etale.forget X).mapCone (Cone.mk (M n) (π n))))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (π n).app (op a) = U.map a.obj.hom.op) ∧
      (∀ n : ℕ,
        ∃ ψ : semiRepresentableMatchingObject (U ⋙ FormalCoproduct.incl.{w} X.Etale) n ≅
            (FormalCoproduct.incl.{w} X.Etale).obj (M n),
          semiRepresentableMatchingMap (U ⋙ FormalCoproduct.incl.{w} X.Etale) n ≫ ψ.hom =
            (FormalCoproduct.incl.{w} X.Etale).map (μ n)) := by
  classical
  choose c μ hzero hlim hfac using etaleFaces X U
  refine ⟨fun n ↦ (c n).pt, fun n ↦ (c n).π, μ, hzero 0 rfl, ?_, hfac, ?_⟩
  · intro n
    let := properFace_finCategory n
    exact ⟨isLimitOfPreserves (Etale.forget X) (hlim n).some⟩
  · intro n
    let F := FormalCoproduct.incl.{w} X.Etale
    obtain ⟨πK, hK, hKfac⟩ := srFaces X (U ⋙ F) n
    let q : Cone (SimplicialObject.properFaceDiagram (U ⋙ F) n) := F.mapCone (c n)
    have hq : IsLimit q := inclLimit (hlim n).some
    let b := hK.some.conePointUniqueUpToIso hq
    refine ⟨b, ?_⟩
    apply hq.hom_ext
    intro a
    rw [Category.assoc, IsLimit.conePointUniqueUpToIso_hom_comp]
    change _ = F.map (μ n) ≫ F.map ((c n).π.app a)
    rw [← F.map_comp, hfac]
    exact hKfac a.unop
private theorem inclCov {X : Scheme.{u}} {A B : X.Etale} (f : A ⟶ B) :
    IsSemiRepresentableCovering ((FormalCoproduct.incl.{w} X.Etale).map f) ↔
      Surjective f.left := by
  constructor
  · intro h
    have hh := (ofArrows_mem_smallEtaleTopology_iff _).mp (h PUnit.unit)
    constructor
    intro y
    have hy : y ∈ (Set.univ : Set B.left) := Set.mem_univ _
    rw [← hh] at hy
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨i, x, hx⟩ := hy
    exact ⟨x, by simpa [FormalCoproduct.incl] using hx⟩
  · intro h j
    apply (ofArrows_mem_smallEtaleTopology_iff _).mpr
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := h.surj y
    refine ⟨⟨PUnit.unit, Subsingleton.elim (α := PUnit) _ _⟩, x, ?_⟩
    simpa [FormalCoproduct.incl] using hx

/-- Matching objects of one-member families are their scheme-theoretic matching schemes.
A simplicial object of `X.Etale` is exactly an augmented simplicial `X`-scheme all of whose
terms are étale over `X`. The cones below are limiting after forgetting to `Over X`, so
universality is tested on all schemes over `X`, rather than only the étale ones. The empty
proper-face diagram in degree zero has the specified vertex `id_X` and its unique matching
map is the augmentation.

Source: Stacks, Tags 01G2, 01G3, 01G5, 0186
(auxiliary; not a blueprint node).

Proof, following the six steps of the node:
1. The small étale category has terminal object `id_X` and scheme-theoretic pullbacks
   [situation-conventions]. Its inclusion into `Over X` preserves
   these, hence finite limits [lem-weil-pbc-finite-limits-from-terminal-pullbacks].
2. Take the matching objects in `X.Etale`. Their boundary cones are also proper-face limits
   [lem-weil-pbc-matching-object-proper-faces, lem-weil-pbc-simplicial-matching-object].
   Preservation gives limiting cones in `Over X`, with étale vertices and matching maps
   whose proper-face components are precisely the simplicial operators.
3. The singleton inclusion preserves terminal objects and pullbacks by the memberwise
   formulas [lem-weil-pbc-semi-representable-finite-limits], hence finite limits by
   [lem-weil-pbc-finite-limits-from-terminal-pullbacks].
4. Apply this to the matching boundary diagram. Limit uniqueness identifies the recorded
   SR matching object with the singleton matching scheme, and identifies their matching
   maps by their face components. In degree zero both vertices are `{id_X}`.
5. Isomorphisms in SR are coverings. Covering permanence
   [lem-weil-pbc-semi-representable-covering-permanence] transports the covering condition
   across the comparison. A singleton is covering exactly when its component is étale and
   surjective. The component is étale since it is a morphism between étale `X`-schemes
   [definition-torsion-sheaves--3].
6. Apply the equivalence in every degree to the definition of an SR hypercover
   [def-weil-pbc-semi-representable-object], obtaining the final equivalence. -/
theorem sr_matching_object_one_member (X : Scheme.{u}) (U : SimplicialObject X.Etale) :
    ∃ (M : ℕ → X.Etale)
      (π : ∀ n : ℕ, (Functor.const _).obj (M n) ⟶ U.properFaceDiagram n)
      (μ : ∀ n : ℕ, U _⦋n⦌ ⟶ M n),
      M 0 = Etale.mk (𝟙 X) ∧
      (∀ n : ℕ,
        Nonempty (IsLimit ((Etale.forget X).mapCone (Cone.mk (M n) (π n))))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (π n).app (op a) = U.map a.obj.hom.op) ∧
      (∀ n : ℕ,
        ∃ ψ : semiRepresentableMatchingObject (U ⋙ FormalCoproduct.incl.{w} X.Etale) n ≅
            (FormalCoproduct.incl.{w} X.Etale).obj (M n),
          semiRepresentableMatchingMap (U ⋙ FormalCoproduct.incl.{w} X.Etale) n ≫ ψ.hom =
            (FormalCoproduct.incl.{w} X.Etale).map (μ n)) ∧
      (∀ n : ℕ,
        IsSemiRepresentableCovering
          (semiRepresentableMatchingMap (U ⋙ FormalCoproduct.incl.{w} X.Etale) n) ↔
            Surjective (μ n).left) ∧
      (IsSemiRepresentableHypercover (U ⋙ FormalCoproduct.incl.{w} X.Etale) ↔
        ∀ n : ℕ, Etale (μ n).left ∧ Surjective (μ n).left) := by
  obtain ⟨M, π, μ, hM0, hlim, hcomp, hiso⟩ := geometry X U
  have hcov (n : ℕ) :
      IsSemiRepresentableCovering
        (semiRepresentableMatchingMap (U ⋙ FormalCoproduct.incl.{w} X.Etale) n) ↔
          Surjective (μ n).left := by
    obtain ⟨ψ, hψ⟩ := hiso n
    constructor
    · intro h
      apply (inclCov (μ n)).mp
      rw [← hψ]
      exact (semiRepresentableCovering_comp_baseChange _ h).1 _ (covering_of_iso ψ)
    · intro h
      have hh := (inclCov.{w} (μ n)).mpr h
      rw [← hψ] at hh
      have hi := (semiRepresentableCovering_comp_baseChange _ hh).1 _
        (covering_of_iso ψ.symm)
      simpa using hi
  refine ⟨M, π, μ, hM0, hlim, hcomp, hiso, hcov, ?_⟩
  constructor
  · intro h n
    exact ⟨inferInstance, (hcov n).mp (h n)⟩
  · intro h n
    exact (hcov n).mpr (h n).2

end AlgebraicGeometry.Scheme
