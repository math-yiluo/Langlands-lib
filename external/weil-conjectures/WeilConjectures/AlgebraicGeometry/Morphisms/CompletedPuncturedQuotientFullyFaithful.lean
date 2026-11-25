/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.RingTheory.Depth
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Regular.Flat
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoPuncturedPrincipalSliceConnected
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletePuncturedPrincipalFormalSections
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
import Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

/-! # Full faithfulness on the punctured completion

## References

* Stacks Project, Tags 0BM6, 0EKS, 0EL8 and 0EII
* Stacks Project, Tag 0BM6, applied in the complete case of Tag 0BLS
* Tags 0AVY, 0ALZ and 0ALJ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem depth_le_of_flat_local {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] :
    IsLocalRing.depth (R := R) R ≤ IsLocalRing.depth (R := S) S := by
  classical
  unfold IsLocalRing.depth Ideal.depth
  simp only [Ideal.smul_eq_mul, Ideal.mul_top,
    ite_eq_right (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    ite_eq_right (IsLocalRing.maximalIdeal.isMaximal S).ne_top]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  have hmem' : ∀ s ∈ rs.map (algebraMap R S), s ∈ IsLocalRing.maximalIdeal S := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact IsLocalRing.map_maximalIdeal_le (algebraMap R S)
      (Ideal.mem_map_of_mem _ (hmem r hr))
  apply le_sSup
  refine ⟨rs.map (algebraMap R S), ?_, hmem', by simp⟩
  exact (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem').mpr
    hreg.toIsWeaklyRegular.of_flat

private theorem finiteEtale_pullback_injective_of_connected
    {X Y : Scheme.{u}} [ConnectedSpace Y] [Nonempty X] (i : X ⟶ Y)
    (P Q : MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ Y) :
    Function.Injective ((MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).map
      (X := P) (Y := Q)) := by
  classical
  let P' : Y.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ P.hom P.prop.2, P.prop.1⟩
  let Q' : Y.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ Q.hom Q.prop.2, Q.prop.1⟩
  intro a b hab
  let a' : P' ⟶ Q' := ⟨MorphismProperty.Over.homMk a.left (MorphismProperty.Over.w a)⟩
  let b' : P' ⟶ Q' := ⟨MorphismProperty.Over.homMk b.left (MorphismProperty.Over.w b)⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let s := X.algClosurePoint x
  let t := s ≫ i
  have he : a' = b' := by
    apply (FiniteEtale.fiber t).map_injective
    apply ConcreteCategory.hom_ext
    intro y
    apply FiniteEtale.fiber_ext
    let c := pullback.lift (f := P.hom) (g := i) y.left s
      (FiniteEtale.fiber_left_comp t y)
    have hh := congrArg (fun k ↦ c ≫ k.left ≫ pullback.fst Q.hom i) hab
    change y.left ≫ a.left = y.left ≫ b.left
    simpa [c, ← Category.assoc, MorphismProperty.Over.pullback_map_left] using hh
  exact MorphismProperty.Over.Hom.ext (congrArg (fun k ↦ k.hom.left) he)

private theorem formal_hom_algebraization
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (V : (Spec (.of R)).Opens)
    (hscalar : ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f V n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f V n).appTop
        (s (n + 1)) = s n) →
      ∃! a : Γ(V.toScheme, ⊤), ∀ n,
        (FiniteEtale.Adic.openThickeningMap f V n).appTop a = s n)
    (P Q : V.toScheme.FiniteEtale)
    (g : ∀ n : ℕ, FiniteEtale.Adic.cover f V P n ⟶ Q.obj.left)
    (hover : ∀ n, g n ≫ Q.obj.hom = FiniteEtale.Adic.coverMap f V P n ≫ P.obj.hom)
    (hcompat : ∀ n, FiniteEtale.Adic.coverTransition f V P n ≫ g (n + 1) = g n) :
    ∃ φ : P.obj.left ⟶ Q.obj.left, φ ≫ Q.obj.hom = P.obj.hom ∧
      ∀ n, FiniteEtale.Adic.coverMap f V P n ≫ φ = g n := by
  classical
  let p (n : ℕ) := FiniteEtale.Adic.coverMap f V P n
  let t (n : ℕ) := FiniteEtale.Adic.coverTransition f V P n
  have hsections := finiteEtale_adic_sections_comparison_of_structureSheaf f V hscalar P
  have hinj (a b : Γ(P.obj.left, ⊤))
      (hab : ∀ n, (p n).appTop a = (p n).appTop b) : a = b := by
    have hc (n : ℕ) : (t n).appTop ((p (n + 1)).appTop a) = (p n).appTop a := by
      change ((p (n + 1)).appTop ≫ (t n).appTop) a = _
      rw [← Scheme.Hom.comp_appTop, FiniteEtale.Adic.coverTransition_coverMap]
    obtain ⟨c, hc', hu⟩ := hsections (fun n ↦ (p n).appTop a) hc
    exact (hu a (fun _ ↦ rfl)).trans (hu b (fun n ↦ (hab n).symm)).symm
  have hfamily (a : Γ(Q.obj.left, ⊤)) (n : ℕ) :
      (t n).appTop ((g (n + 1)).appTop a) = (g n).appTop a := by
    change ((g (n + 1)).appTop ≫ (t n).appTop) a = _
    rw [← Scheme.Hom.comp_appTop, hcompat]
  have hex (a : Γ(Q.obj.left, ⊤)) :
      ∃ b : Γ(P.obj.left, ⊤), ∀ n, (p n).appTop b = (g n).appTop a :=
    (hsections (fun n ↦ (g n).appTop a) (hfamily a)).exists
  choose b hb using hex
  let α : Γ(Q.obj.left, ⊤) →+* Γ(P.obj.left, ⊤) :=
    { toFun := b
      map_one' := by
        apply hinj
        intro n
        rw [hb, map_one, map_one]
      map_mul' := by
        intro a a'
        apply hinj
        intro n
        rw [hb, map_mul, map_mul, hb, hb]
      map_zero' := by
        apply hinj
        intro n
        rw [hb, map_zero, map_zero]
      map_add' := by
        intro a a'
        apply hinj
        intro n
        rw [hb, map_add, map_add, hb, hb] }
  let α' := CommRingCat.ofHom α
  have hα (n : ℕ) : α' ≫ (p n).appTop = (g n).appTop := by
    ext a
    exact hb a n
  have hbase : Q.obj.hom.appTop ≫ α' = P.obj.hom.appTop := by
    ext a
    apply hinj
    intro n
    change (Q.obj.hom.appTop ≫ α' ≫ (p n).appTop) a =
      (P.obj.hom.appTop ≫ (p n).appTop) a
    rw [hα, ← Scheme.Hom.comp_appTop, hover, Scheme.Hom.comp_appTop]
    rfl
  have : TopologicalSpace.NoetherianSpace (Spec (.of R)) := inferInstance
  have : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace V.toScheme := TopologicalSpace.NoetherianSpace.compactSpace V.toScheme
  have : V.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion V.ι
  have : IsFinite Q.obj.hom := Q.property
  let q : Q.obj.left ⟶ V.toScheme := Q.obj.hom
  have : IsAffineHom q := inferInstanceAs (IsAffineHom Q.obj.hom)
  have : Q.obj.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom q
  let square := isPullback_toSpecΓ_toSpecΓ q
  have hw : P.obj.hom ≫ V.toScheme.toSpecΓ =
      (P.obj.left.toSpecΓ ≫ Spec.map α') ≫ Spec.map Q.obj.hom.appTop := by
    rw [Category.assoc, ← Spec.map_comp, hbase]
    exact Scheme.toSpecΓ_naturality P.obj.hom
  let φ := square.lift P.obj.hom (P.obj.left.toSpecΓ ≫ Spec.map α') hw
  refine ⟨φ, square.lift_fst _ _ _, ?_⟩
  intro n
  apply (cancel_mono Q.obj.left.toSpecΓ).mp
  change p n ≫ (φ ≫ Q.obj.left.toSpecΓ) = g n ≫ Q.obj.left.toSpecΓ
  rw [show φ ≫ Q.obj.left.toSpecΓ = P.obj.left.toSpecΓ ≫ Spec.map α' from
    square.lift_snd _ _ _]
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp, hα, ← Scheme.toSpecΓ_naturality]


set_option backward.isDefEq.respectTransparency false in
private theorem complete_punctured_quotient_restriction_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {g})))
    ∀ P Q : MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ W.toScheme,
      Function.Surjective ((MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤
        (j ∣_ W)).map (X := P) (Y := Q)) := by
  classical
  dsimp only
  intro P Q φ
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let P' : W.toScheme.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ P.hom P.prop.2, P.prop.1⟩
  let Q' : W.toScheme.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ Q.hom Q.prop.2, Q.prop.1⟩
  let φ' : (FiniteEtale.pullback ((Spec.map (CommRingCat.ofHom f)) ∣_ W)).obj P' ⟶
      (FiniteEtale.pullback ((Spec.map (CommRingCat.ofHom f)) ∣_ W)).obj Q' :=
    ⟨MorphismProperty.Over.homMk φ.left (MorphismProperty.Over.w φ)⟩
  have hlift (n : ℕ) := finiteEtale_adic_unique_lift f Ideal.Quotient.mk_surjective W P' Q' φ' n
  choose a ha huniq using hlift
  have hcompat (n : ℕ) :
      FiniteEtale.Adic.coverTransition f W P' n ≫ a (n + 1) = a n := by
    apply huniq n
    constructor
    · rw [Category.assoc, (ha (n + 1)).1, ← Category.assoc,
        FiniteEtale.Adic.coverTransition_coverMap]
    · rw [← Category.assoc, FiniteEtale.Adic.zeroMap_coverTransition, (ha (n + 1)).2]
  obtain ⟨ψ, hψ, hformal⟩ := formal_hom_algebraization f W
    (complete_punctured_principal_formal_sections R g hg hdepth W hW)
    P' Q' a (fun n ↦ (ha n).1) hcompat
  let Ψ : P ⟶ Q := MorphismProperty.Over.homMk ψ hψ
  refine ⟨Ψ, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    change pullback.fst P'.obj.hom ((Spec.map (CommRingCat.ofHom f)) ∣_ W) ≫ ψ =
      φ'.hom.left ≫ pullback.fst Q'.obj.hom ((Spec.map (CommRingCat.ofHom f)) ∣_ W)
    rw [← FiniteEtale.Adic.zeroMap_coverMap f W P' 0, Category.assoc, hformal 0]
    exact (ha 0).2
  · simpa only [MorphismProperty.Over.pullback_map_left,
      pullback.lift_snd, Category.comp_id, MorphismProperty.Over.pullback_obj_hom]
      using (MorphismProperty.Over.w φ).symm

/-- Quotient restriction of finite etale covers of the punctured completion is fully faithful.
-/
theorem fullyFaithful_completed_punctured_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let W := c ⁻¹ᵁ U
    let j := Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {algebraMap A C f})))
    Nonempty (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤
      (j ∣_ W)).FullyFaithful := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let W := c ⁻¹ᵁ U
  let : IsNoetherianRing C := AdicCompletion.isNoetherianRing _
  have hdepthC : (3 : ℕ∞) ≤ IsLocalRing.depth (R := C) C :=
    hdepth.trans (depth_le_of_flat_local (R := A) (S := C))
  have hfC : algebraMap A C f ∈ IsLocalRing.maximalIdeal C :=
    IsLocalRing.map_maximalIdeal_le (algebraMap A C) (Ideal.mem_map_of_mem _ hf)
  have hclosed (x : Spec (.of C)) : c x = IsLocalRing.closedPoint A ↔
      x = IsLocalRing.closedPoint C := by
    constructor
    · intro hx
      have heq : x.asIdeal.comap (algebraMap A C) = IsLocalRing.maximalIdeal A :=
        congrArg PrimeSpectrum.asIdeal hx
      apply PrimeSpectrum.ext
      apply le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime x.asIdeal)
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.map_le_iff_le_comap.mpr heq.ge
    · rintro rfl
      exact IsLocalRing.comap_closedPoint (algebraMap A C)
  have hW : ∀ x : Spec (.of C), x ∈ W ↔ x ≠ IsLocalRing.closedPoint C := by
    intro x
    exact (hU (c x)).trans (not_congr (hclosed x))
  obtain ⟨hconn, hnonempty⟩ := depth_two_punctured_principal_slice_connected C
    (algebraMap A C f) hfC ((by decide : (2 : ℕ∞) ≤ 3).trans hdepthC) W hW
  let := hconn
  let := hnonempty
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
  intro P Q
  exact ⟨finiteEtale_pullback_injective_of_connected _ P Q,
    complete_punctured_quotient_restriction_surjective C (algebraMap A C f) hfC
      hdepthC W hW P Q⟩

end AlgebraicGeometry.Scheme
