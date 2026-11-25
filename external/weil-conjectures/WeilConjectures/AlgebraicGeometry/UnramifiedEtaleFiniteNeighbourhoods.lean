/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints
import WeilConjectures.AlgebraicGeometry.UnramifiedFibrePointIsolated
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen

/-!
# Finite unramified neighbourhoods after étale localization

The first construction in Stacks Project, Tag 04HI, using Tags 02LM, 02G6 and 02GA.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Source-locality on the explicit cover by the original opens.
private theorem unramified_union {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type*} (O : ι → X.Opens)
    (hO : ∀ i, LocallyOfFiniteType ((O i).ι ≫ f) ∧
      IsOpenImmersion (pullback.diagonal ((O i).ι ≫ f))) :
    LocallyOfFiniteType ((⨆ i, O i).ι ≫ f) ∧
      IsOpenImmersion (pullback.diagonal ((⨆ i, O i).ι ≫ f)) := by
  classical
  let W : X.Opens := ⨆ i, O i
  let C : W.toScheme.OpenCover :=
    { I₀ := ι
      X i := (O i).toScheme
      f i := Scheme.homOfLE X (le_iSup O i)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨?_, inferInstance⟩
        intro z
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp z.property
        exact ⟨i, ⟨⟨z.val, hi⟩, Subtype.ext (by simp)⟩⟩ }
  have hl : LocallyOfFiniteType (W.ι ≫ f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) C
    intro i
    simpa [C, W, ← Category.assoc] using (hO i).1
  have hf : FormallyUnramified (W.ι ≫ f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @FormallyUnramified) C
    intro i
    have : IsOpenImmersion (pullback.diagonal ((O i).ι ≫ f)) := (hO i).2
    have : FormallyUnramified ((O i).ι ≫ f) := inferInstance
    simpa [C, W, ← Category.assoc] using this
  let := hl
  let := hf
  exact ⟨hl, inferInstance⟩

-- Identify each finite open with its open image in the larger ambient scheme.
private theorem exists_finite_marked_open_immersion_transport
    {Y Z U : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ U)
    (q : Y ⟶ U) (hcomm : j ≫ p = q)
    (hj : LocallyOfFiniteType q ∧ IsOpenImmersion (pullback.diagonal q))
    (u : U) (W : Y.Opens) (w : W.toScheme)
    (hfinite : IsFinite (W.ι ≫ q))
    (hw : (W.ι ≫ q) w = u)
    (hunique : ∀ z : W.toScheme, (W.ι ≫ q) z = u → z = w)
    (hpure : letI := ((W.ι ≫ q).residueFieldMap w).hom.toAlgebra
      IsPurelyInseparable (U.residueField ((W.ι ≫ q) w)) (W.toScheme.residueField w)) :
    ∃ (V : Z.Opens) (v : V.toScheme),
      IsFinite (V.ι ≫ p) ∧
      (LocallyOfFiniteType (V.ι ≫ p) ∧ IsOpenImmersion (pullback.diagonal (V.ι ≫ p))) ∧
      (V.ι ≫ p) v = u ∧
      (∀ z : V.toScheme, (V.ι ≫ p) z = u → z = v) ∧
      (letI := ((V.ι ≫ p).residueFieldMap v).hom.toAlgebra
       IsPurelyInseparable (U.residueField ((V.ι ≫ p) v)) (V.toScheme.residueField v)) ∧
      V.ι v = j (W.ι w) := by
  classical
  let k := W.ι ≫ j
  let V := k.opensRange
  let e : W.toScheme ≅ V.toScheme := k.isoOpensRange
  let v := e.hom w
  have he : e.hom ≫ V.ι = k := k.isoOpensRange_hom_ι
  have heq : e.hom ≫ V.ι ≫ p = W.ι ≫ q := by
    rw [← Category.assoc, he]
    simp [k, hcomm]
  have heinv : V.ι ≫ p = e.inv ≫ W.ι ≫ q := by
    rw [← heq]
    simp
  have hf : IsFinite (V.ι ≫ p) := by
    rw [heinv]
    have : IsFinite (W.ι ≫ q) := hfinite
    infer_instance
  have hl : LocallyOfFiniteType (V.ι ≫ p) := by
    rw [heinv]
    have : LocallyOfFiniteType q := hj.1
    infer_instance
  have hdiag : IsOpenImmersion (pullback.diagonal (V.ι ≫ p)) := by
    rw [heinv]
    have : LocallyOfFiniteType q := hj.1
    have : IsOpenImmersion (pullback.diagonal q) := hj.2
    have hq : FormallyUnramified q := inferInstance
    have hW : FormallyUnramified (W.ι ≫ q) := IsZariskiLocalAtSource.comp hq _
    have : FormallyUnramified (e.inv ≫ W.ι ≫ q) :=
      IsZariskiLocalAtSource.comp hW _
    infer_instance
  have hv : (V.ι ≫ p) v = u := by
    change (e.hom ≫ V.ι ≫ p) w = u
    rw [heq]
    exact hw
  refine ⟨V, v, hf, ⟨hl, hdiag⟩, hv, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : (W.ι ≫ q) (e.inv z) = u := by
      change (e.inv ≫ W.ι ≫ q) z = u
      rw [← heinv]
      exact hz
    have := hunique (e.inv z) hz'
    have := congrArg e.hom this
    simpa [v] using this
  · have hp := hpure
    rw [← heq, Scheme.residueFieldMap_comp] at hp
    let F := U.residueField ((V.ι ≫ p) v)
    let E := V.toScheme.residueField v
    let K := W.toScheme.residueField w
    let a : F ⟶ E := (V.ι ≫ p).residueFieldMap v
    let b : E ⟶ K := e.hom.residueFieldMap w
    algebraize [a.hom, b.hom, (a ≫ b).hom]
    have : IsScalarTower F E K := IsScalarTower.of_algebraMap_eq' (by rfl)
    have : IsPurelyInseparable F K := hp
    exact IsPurelyInseparable.tower_bot F E K
  · change (e.hom ≫ V.ι) w = j (W.ι w)
    rw [he]
    rfl

-- The conclusion imposes no relation between a piece and its first output index.
private theorem index_finite_family {A : Type u} [Finite A] (n : ℕ) :
    ∃ m : Fin (n + 1) → ℕ, Nonempty ((Σ i, Fin (m i)) ≃ A) := by
  classical
  let := Fintype.ofFinite A
  let m : Fin (n + 1) → ℕ := fun i ↦ if i = 0 then Fintype.card A else 0
  have hi (a : Σ i, Fin (m i)) : a.1 = 0 := by
    by_contra h
    have := a.2.isLt
    simp [m, h] at this
  let e : (Σ i, Fin (m i)) ≃ Fin (Fintype.card A) :=
    { toFun a := ⟨a.2.val, by simpa [m, hi a] using a.2.isLt⟩
      invFun a := ⟨0, ⟨a.val, by simp [m]⟩⟩
      left_inv a := by
        obtain ⟨i, j⟩ := a
        have h : i = 0 := hi ⟨i, j⟩
        subst i
        rfl
      right_inv a := rfl }
  exact ⟨m, ⟨e.trans (Fintype.equivFin A).symm⟩⟩

/-- Source: Stacks Project, Tag 04HH, used by Tag 04HI; Tag 02LM and Tags 02G6, 02GA.
(blueprint: lem-weil-pbc-unramified-etale-finite-neighbourhoods)

Proof: take the union of the given unramified open neighbourhoods. Local finite type and
unramifiedness are local on the source, so its restriction is unramified. Remove duplicate
listed points, keeping one representative index for each. The isolated-fibre-point theorem
applies to this restriction. Apply `exists_etale_local_finite_multiple_points` to the distinct
representatives. Its finite pieces remain unramified by base change and open restriction.
The open immersion from the restricted source induces an open immersion of pullbacks;
regard the pieces as opens of the original pullback. Open immersions identify their residue
fields, so uniqueness and pure inseparability persist. For a nonempty original list, put
all pieces in its first output row and give every other row size zero, using an equivalence
of finite index types. The injectivity of the marked points is unchanged. Every lift of a
listed point lies in this source open and is one of the enumerated points, including for
repeated entries of the original list. For the empty list retain the obtained neighbourhood
and take the empty family. -/
theorem exists_etale_finite_unramified_neighbourhoods
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (n : ℕ) (x : Fin n → X) (hx : ∀ i, f.base (x i) = s)
    (hunramified : ∀ i, ∃ O : X.Opens, x i ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (O.ι ≫ f))) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g.base u = s ∧
      ∃ (m : Fin n → ℕ) (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens)
        (v : (a : Σ i : Fin n, Fin (m i)) → (V a).toScheme),
        (∀ a, IsFinite ((V a).ι ≫ pullback.snd f g) ∧
          (LocallyOfFiniteType ((V a).ι ≫ pullback.snd f g) ∧
            IsOpenImmersion (pullback.diagonal ((V a).ι ≫ pullback.snd f g))) ∧
          ((V a).ι ≫ pullback.snd f g) (v a) = u ∧
          (∀ w : (V a).toScheme,
            ((V a).ι ≫ pullback.snd f g) w = u → w = v a) ∧
          (letI : Algebra (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
              ((V a).toScheme.residueField (v a)) :=
            (((V a).ι ≫ pullback.snd f g).residueFieldMap (v a)).hom.toAlgebra
           IsPurelyInseparable
             (U.residueField (((V a).ι ≫ pullback.snd f g) (v a)))
             ((V a).toScheme.residueField (v a)))) ∧
        Function.Injective (fun a ↦ (V a).ι (v a)) ∧
        (∀ (i : Fin n) (p : ↥(pullback f g)),
          (pullback.snd f g).base p = u → (pullback.fst f g).base p = x i →
            ∃ a, p = (V a).ι (v a)) := by
  classical
  choose O hmem hl hd using hunramified
  have hO (i : Fin n) := And.intro (hl i) (hd i)
  let T : X.Opens := ⨆ i, O i
  have hxT (i : Fin n) : x i ∈ T :=
    TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hmem i⟩
  have hT := unramified_union f O hO
  let fT : T.toScheme ⟶ S := T.ι ≫ f
  have : LocallyOfFiniteType fT := hT.1
  let xT : Fin n → T.toScheme := fun i ↦ ⟨x i, hxT i⟩
  let R := Set.range xT
  let e := (Fintype.equivFin R).symm
  let y : Fin (Fintype.card R) → T.toScheme := fun i ↦ (e i).val
  have hy (i : Fin (Fintype.card R)) : fT (y i) = s := by
    obtain ⟨a, ha⟩ := (e i).property
    dsimp [y]
    rw [← ha]
    exact hx a
  have hinj : Function.Injective y := Subtype.val_injective.comp e.injective
  have hiso (i : Fin (Fintype.card R)) :
      IsOpen ({fT.asFiber (y i)} : Set (fT.fiber (fT (y i)))) := by
    apply (unramified_fibre_point_isolated fT (y i) _).1
    refine ⟨⊤, trivial, ?_⟩
    have : IsOpenImmersion (pullback.diagonal fT) := hT.2
    have : FormallyUnramified fT := inferInstance
    have : FormallyUnramified ((⊤ : T.toScheme.Opens).ι ≫ fT) :=
      IsZariskiLocalAtSource.comp (inferInstanceAs (FormallyUnramified fT)) _
    exact ⟨inferInstance, inferInstance⟩
  obtain ⟨U, g, u, hg, hus, m, W, w, hW, hw_inj, hex⟩ :=
    exists_etale_local_finite_multiple_points fT s _ y hy hinj hiso
  let j : pullback fT g ⟶ pullback f g :=
    pullback.map fT g f g T.ι (𝟙 _) (𝟙 S) (by simp [fT]) (by simp)
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hj : j ≫ pullback.snd f g = pullback.snd fT g := by simp [j]
  have hjfst : j ≫ pullback.fst f g = pullback.fst fT g ≫ T.ι := by simp [j]
  have hun := unramified_baseChange_restrict_open fT hT g
  have hpieces (a : Σ i, Fin (m i)) :
      ∃ (V : (pullback f g).Opens) (v : V.toScheme),
        IsFinite (V.ι ≫ pullback.snd f g) ∧
        (LocallyOfFiniteType (V.ι ≫ pullback.snd f g) ∧
          IsOpenImmersion (pullback.diagonal (V.ι ≫ pullback.snd f g))) ∧
        (V.ι ≫ pullback.snd f g) v = u ∧
        (∀ z : V.toScheme, (V.ι ≫ pullback.snd f g) z = u → z = v) ∧
        (letI := ((V.ι ≫ pullback.snd f g).residueFieldMap v).hom.toAlgebra
         IsPurelyInseparable (U.residueField ((V.ι ≫ pullback.snd f g) v))
           (V.toScheme.residueField v)) ∧
        V.ι v = j ((W a.1 a.2).ι (w a.1 a.2)) := by
    obtain ⟨hf, hv, hu, hp, _⟩ := hW a.1 a.2
    apply exists_finite_marked_open_immersion_transport j
      (pullback.snd f g) (pullback.snd fT g) hj
      ⟨hun.1, hun.2.1⟩
      u (W a.1 a.2) (w a.1 a.2)
    · exact hf
    · exact hv
    · exact hu
    · have hp' := hp.2
      cases hv
      simpa using hp'
  choose V v hV using hpieces
  have hvinj : Function.Injective (fun a ↦ (V a).ι (v a)) := by
    intro a b hab
    apply hw_inj
    apply j.isOpenEmbedding.injective
    simpa only [(hV a).2.2.2.2.2, (hV b).2.2.2.2.2] using hab
  have hexV (i : Fin n) (p : ↥(pullback f g))
      (hpu : (pullback.snd f g) p = u) (hpx : (pullback.fst f g) p = x i) :
      ∃ a, p = (V a).ι (v a) := by
    have hpj : p ∈ Set.range j := by
      dsimp [j]
      rw [Scheme.Pullback.range_map]
      exact ⟨⟨xT i, by simpa [xT] using hpx.symm⟩, ⟨_, rfl⟩⟩
    obtain ⟨q, hq⟩ := hpj
    let r : R := ⟨xT i, ⟨i, rfl⟩⟩
    have hyr : y (e.symm r) = xT i := by simp [y, r]
    have hqu : (pullback.snd fT g) q = u := by
      rw [← hj]
      simpa [hq] using hpu
    have hqx : (pullback.fst fT g) q = y (e.symm r) := by
      rw [hyr]
      apply T.ι.isOpenEmbedding.injective
      change (pullback.fst fT g ≫ T.ι) q = x i
      rw [← hjfst]
      simpa [hq] using hpx
    obtain ⟨b, hb⟩ := hex (e.symm r) q hqu hqx
    refine ⟨⟨e.symm r, b⟩, ?_⟩
    rw [(hV ⟨e.symm r, b⟩).2.2.2.2.2, ← hb, hq]
  cases n with
  | zero =>
      refine ⟨U, g, u, hg, hus, fun i ↦ Fin.elim0 i,
        (fun a ↦ Fin.elim0 a.1), (fun a ↦ Fin.elim0 a.1), ?_, ?_, ?_⟩
      · intro a; exact Fin.elim0 a.1
      · intro a; exact Fin.elim0 a.1
      · intro i; exact Fin.elim0 i
  | succ n =>
      obtain ⟨m', ⟨e'⟩⟩ := index_finite_family (A := Σ i, Fin (m i)) n
      refine ⟨U, g, u, hg, hus, m', (fun a ↦ V (e' a)),
        (fun a ↦ v (e' a)), ?_, hvinj.comp e'.injective, ?_⟩
      · intro a
        exact ⟨(hV (e' a)).1, (hV (e' a)).2.1, (hV (e' a)).2.2.1,
          (hV (e' a)).2.2.2.1, (hV (e' a)).2.2.2.2.1⟩
      · intro i p hpu hpx
        obtain ⟨a, ha⟩ := hexV i p hpu hpx
        refine ⟨e'.symm a, ?_⟩
        change p = (V (e' (e'.symm a))).ι (v (e' (e'.symm a)))
        exact ha.trans (congrArg (fun b ↦ (V b).ι (v b))
          (e'.apply_symm_apply a)).symm

end AlgebraicGeometry
