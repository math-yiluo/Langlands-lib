/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module



public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing


public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Topology.Spectral.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
public import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting
public import WeilConjectures.RingTheory.IntegralOverHenselianPair
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction


/-!
# Connectedness of closed fibres of proper schemes over a henselian pair

Let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` a proper morphism, with closed fibre
`Y₀ = p⁻¹(V(I))`. This file records the two classical inputs of the degree-zero comparison
`Γ(Y, F) ≅ Γ(Y₀, F|_{Y₀})`:

* (i) *finiteness*: in the Stein factorization `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec A`, the second map is
  finite. This is stated for a noetherian `A`, where it is the coherence of `p_* 𝒪_Y`;
* (ii) *connectedness*: every irreducible closed subset `C ⊆ Y` meets `Y₀` in a nonempty
  connected subset.

Together with the spectrality of `Y` and the closedness of `Y₀`, input (ii) is exactly the
hypothesis of the Zariski restriction criterion
`TopCat.Sheaf.bijective_unit_app_top` for the pair `(Y, Y₀)`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isFinite_steinFactorizationBase`: input (i).
- `AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`: input (ii).
- `AlgebraicGeometry.Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter`: the
  hypotheses of the Zariski restriction criterion for `(Y, Y₀)`.

## References

- Stacks Project, Lemma 59.91.1, <https://stacks.math.columbia.edu/tag/0A0B>
- Stacks Project, Theorem 37.53.5, <https://stacks.math.columbia.edu/tag/03H2>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Finiteness of the Stein factorization** (input (i) of the two classical inputs of
Stein connectedness): for a proper morphism `p : Y ⟶ Spec A` with `A` noetherian, the ring
`Γ(Y, 𝒪_Y)` is a finite `A`-algebra, i.e. the second map `Spec Γ(Y, 𝒪_Y) ⟶ Spec A` of the Stein
factorization is finite. For a general affine base this is not proved in the blueprint.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) 
(blueprint: theorem-comparison-over-henselian-pair-degree)
-/
@[stacks 02O5]
theorem Scheme.Hom.isFinite_steinFactorizationBase {A : Type u} [CommRing A]
    [IsNoetherianRing A] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p] :
    IsFinite p.steinFactorizationBase := by
  have := Modules.isGrothendieckAbelian Y
  have : IsNoetherianRing Γ(Spec (.of A), ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  have : (SheafOfModules.unit Y.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  obtain ⟨e, he⟩ := Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H p O 0
  have := Modules.finite_sections_higherDirectImage p O 0
  let := p.appTop.hom.toAlgebra
  let e' : Γ((Modules.higherDirectImage p 0).obj O, ⊤) →ₗ[Γ(Spec (.of A), ⊤)] Γ(Y, ⊤) :=
    { toFun x := Modules.H.zeroLinearEquiv O (e x)
      map_add' x y := by simp
      map_smul' a x := by
        rw [e.map_smulₛₗ, LinearEquiv.map_smul]
        rfl }
  have hp : p.appTop.hom.Finite :=
    Module.Finite.of_surjective e' ((Modules.H.zeroLinearEquiv O).surjective.comp he.2)
  rw [Scheme.Hom.steinFactorizationBase, IsFinite.SpecMap_iff, CommRingCat.hom_comp]
  exact hp.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)

/-- Every nonempty closed subset `C` of a scheme proper over `Spec A` meets the
closed fibre over `V(I)` when `I` lies in the Jacobson radical: the image of `C` is closed, so
it contains a closed point of `Spec A`, i.e. a maximal ideal, which contains `I`. This is the
nonemptiness half of `AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`. -/
theorem Scheme.Hom.nonempty_inter_preimage_zeroLocus {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    [IsProper p] {C : Set Y} (hC : IsClosed C) (hne : C.Nonempty) :
    (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)).Nonempty := by
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ :=
    (p.isClosedMap C hC).exists_closed_singleton (hne.image p)
  have hmax : (p y : PrimeSpectrum A).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hx
  refine ⟨y, hy, ?_⟩
  change (I : Set A) ⊆ (p y : PrimeSpectrum A).asIdeal
  exact fun a ha ↦ Ideal.mem_sInf.mp (hI ha) ⟨bot_le, hmax⟩

/-- **Connectedness of the closed fibre** (input (ii) of the two classical inputs of Stein
connectedness): let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` proper. Every
irreducible closed subset `C ⊆ Y` meets the closed fibre `Y₀ = p⁻¹(V(I))` in a nonempty
connected subset. This is the Stein-factorization step of the henselian-pair comparison
[Stacks 0A0B].

It is deduced from the idempotent lifting for proper schemes over a henselian pair
(`AlgebraicGeometry.Scheme.bijective_appTop_idempotent_of_henselianRing`, blueprint
`theorem-finite-etale-covers-proper-henselian--2`), applied to `C` with its reduced induced
structure `Z`: the space `Z ≅ C` is irreducible, hence connected, so `Γ(Z, 𝒪_Z)` has no
idempotents but `0` and `1`; hence neither has `Γ(Z₀, 𝒪_{Z₀})`, and the nonempty closed fibre
`Z₀`, whose image in `Y` is `C ∩ Y₀`, is connected.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) 
(blueprint: theorem-comparison-over-henselian-pair-degree)
-/
@[stacks 0A0B]
theorem Scheme.Hom.isConnected_inter_preimage_zeroLocus {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    {C : Set Y} (hC : IsClosed C) (hC' : IsIrreducible C) :
    IsConnected (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
  have hne := p.nonempty_inter_preimage_zeroLocus I HenselianRing.jac hC hC'.nonempty
  -- The reduced induced closed subscheme on `C`.
  let J := Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨C, hC⟩
  let Z := J.subscheme
  let ι : Z ⟶ Y := J.subschemeι
  have hι : Set.range ι = C := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  let q : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hq : Set.range q = PrimeSpectrum.zeroLocus (I : Set A) := by
    have := range_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at this
    exact this
  let Z₀ := pullback (ι ≫ p) q
  let i₀ : Z₀ ⟶ Z := pullback.fst _ _
  have hrange : Set.range (i₀ ≫ ι) = C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst,
      ← hq, ← hι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      Set.image_preimage_eq_range_inter, Set.inter_comm]
  rw [← hrange]
  have : ConnectedSpace Z := by
    have : IrreducibleSpace Z := Subtype.irreducibleSpace (s := (J.support : Set Y)) (by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hC')
    infer_instance
  have : Nonempty Z₀ := by
    obtain ⟨y, hyC, hy₀⟩ := hne
    rw [← hι] at hyC
    obtain ⟨z, rfl⟩ := hyC
    rw [← hq] at hy₀
    obtain ⟨x, hx⟩ := hy₀
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ι ≫ p) (g := q) z x
      (by simpa using hx.symm)
    exact ⟨w⟩
  have : Nonempty Z := ⟨i₀ (Classical.arbitrary Z₀)⟩
  let g := ι ≫ p
  obtain ⟨hi, hp, hgc, hfib⟩ := g.steinFactorization_affine
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨Classical.arbitrary Z, trivial⟩⟩
  let B := Γ(Z, ⊤)
  have : Nontrivial B := Scheme.component_nontrivial Z ⊤
  let α : A →+* B := ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom
  let : Algebra A B := α.toAlgebra
  have : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp hi
  let IB := I.map (algebraMap A B)
  have : HenselianRing B IB := henselianRing_of_isIntegral A I B
  have hIB : IB ≠ ⊤ := by
    intro h
    have hj : Ideal.jacobson (⊥ : Ideal B) = ⊤ :=
      top_le_iff.mp (h ▸ HenselianRing.jac (R := B) (I := IB))
    exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp hj)
  have : Nontrivial (B ⧸ IB) := Ideal.Quotient.nontrivial_iff.mpr hIB
  have : ConnectedSpace (PrimeSpectrum (B ⧸ IB)) := by
    apply PrimeSpectrum.connectedSpace_of_isIdempotentElem
    intro e he
    obtain ⟨e', ⟨he', hee'⟩, -⟩ :=
      Algebra.existsUnique_isIdempotentElem_of_henselianRing A I B e he
    rcases (Scheme.connectedSpace_iff_isIdempotentElem Z).1 inferInstance e' he' with h | h
    · left
      simpa only [h, map_zero] using hee'.symm
    · right
      simpa only [h, map_one] using hee'.symm
  have hIBconn : _root_.IsConnected (PrimeSpectrum.zeroLocus (IB : Set B)) := by
    have h := isConnected_range (PrimeSpectrum.continuous_comap (Ideal.Quotient.mk IB))
    simpa [range_comap_of_surjective (B ⧸ IB) (Ideal.Quotient.mk IB)
      Ideal.Quotient.mk_surjective, Ideal.mk_ker] using h
  let : IsProper Z.toSpecΓ := hp
  let : GeometricallyConnected Z.toSpecΓ := hgc
  have hconn : _root_.IsConnected (Z.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus (IB : Set B)) :=
    Topology.IsCoinducing.isConnected_preimage_of_isClosed
      (fun t ↦ (hfib t).2)
      (Z.toSpecΓ.isClosedMap.isQuotientMap Z.toSpecΓ.continuous
        Z.toSpecΓ.surjective).isCoinducing
      (PrimeSpectrum.isClosed_zeroLocus _) hIBconn
  have hpre : g ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) =
      Z.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus (IB : Set B) := by
    rw [← Scheme.toSpecΓ_steinFactorizationBase g, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.preimage_comp]
    congr 1
    change PrimeSpectrum.comap α ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus]
    change PrimeSpectrum.zeroLocus (α '' (I : Set A)) =
      PrimeSpectrum.zeroLocus (I.map α : Set B)
    rw [Ideal.map, PrimeSpectrum.zeroLocus_span]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.Pullback.range_fst, hq, hpre]
  exact hconn.image ι ι.continuous.continuousOn

/-- **Stein connectedness.** Let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` proper, with
closed fibre `Y₀ = p⁻¹(V(I))`. Then `Y` is a spectral space, `Y₀` is closed in `Y`, and every
irreducible closed subset of `Y` meets `Y₀` in a nonempty connected subset. These are the
hypotheses of the Zariski restriction criterion
`TopCat.Sheaf.bijective_unit_app_top` for the pair `(Y, Y₀)`. The
spectrality holds because `Y` is quasi-compact and quasi-separated, the closedness because
`V(I)` is closed, and the connectedness is the classical input
`AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`.
(blueprint: `theorem-comparison-over-henselian-pair-degree`) 
(blueprint: theorem-comparison-over-henselian-pair-degree)
-/
theorem Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p] :
    SpectralSpace Y ∧ IsClosed (p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) ∧
      ∀ C : Set Y, IsClosed C → IsIrreducible C →
        IsConnected (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  exact ⟨{}, (PrimeSpectrum.isClosed_zeroLocus _).preimage p.continuous,
    fun C hC hC' ↦ p.isConnected_inter_preimage_zeroLocus I hC hC'⟩

end AlgebraicGeometry
