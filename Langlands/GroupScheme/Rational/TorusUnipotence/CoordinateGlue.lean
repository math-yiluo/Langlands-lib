import Langlands.GroupScheme.Rational.TorusUnipotence.Regrading
import Langlands.GroupScheme.Rational.TorusUnipotence.CoordinateGrading
import Langlands.GroupScheme.Rational.TorusUnipotence.CotangentBasis
import Langlands.GroupScheme.Rational.TorusUnipotenceStatement
import Langlands.GroupScheme.Rational.CoordinateCotangentSupportProof
import Langlands.GroupScheme.Rational.CoordinateSemigroupReduction
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Dynamic.SmoothProof

/-! # Unipotence of split torus actions without a zero Lie weight -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusUnipotence

section Finite

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k)

theorem cotangentMap_mul_of_mem (a : A) {x : A} (hx : x ∈ RingHom.ker ε) :
    cotangentMap ε (a * x) = ε a • cotangentMap ε x := by
  rw [cotangentMap_mul, show ε x = 0 from hx, zero_smul, add_zero]

/-- The augmentation cotangent space of a Noetherian augmented algebra is finite-dimensional. -/
theorem finite_cotangent [IsNoetherianRing A] : Module.Finite k (RingHom.ker ε).Cotangent := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (R := A) (M := A) (RingHom.ker ε)
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨cotangentMap ε '' s, s.finite_toSet.image _, eq_top_iff.2 ?_⟩
  rintro q -
  obtain ⟨⟨x, hx⟩, rfl⟩ := (RingHom.ker ε).toCotangent_surjective q
  rw [← cotangentMap_of_mem ε hx]
  have hx' : x ∈ Submodule.span A (s : Set A) := hs.symm ▸ hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y hy' hy =>
    rw [smul_eq_mul, cotangentMap_mul_of_mem ε a (hs.le hy')]
    exact Submodule.smul_mem _ _ hy

end Finite

section Group

open CoordinateWeights

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "A" => CharacterUnits.Coord H

theorem augmentationIdeal_eq_ker : augmentationIdeal H = RingHom.ker (coordCounit H) := rfl

theorem finite_cotangentSupport [LocallyOfFiniteType H.X.hom] (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp H) : (cotangentSupport b).Finite := by
  classical
  have := isNoetherianRing_coord (G := H)
  have : Module.Finite k (Cotangent H) := finite_cotangent (coordCounit H)
  have hind : iSupIndep (cotangentWeightSpace b) :=
    (coordinateWeightDecomposition k H inferInstance S hS b).2.2.1.submodule_iSupIndep
  refine (WellFoundedGT.finite_ne_bot_of_iSupIndep hind).subset ?_
  rintro χ ⟨q, hq, hqw⟩ hbot
  exact hq ((Submodule.mem_bot k).1 (hbot ▸ hqw))

theorem cotangentWeightSpace_eq_bot (b : AutomorphicAction S.toGrp H) {χ : characterLattice S}
    (hχ : χ ∉ cotangentSupport b) : cotangentWeightSpace b χ = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun q hq => by
    by_contra hq0
    exact hχ ⟨q, hq0, hq⟩

/-- A coordinate eigenfunction killed by the counit whose character is outside the cotangent
support lies in the square of the augmentation ideal. -/
theorem mem_sq_of_not_mem_cotangentSupport (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp H) {χ : characterLattice S} (hχ : χ ∉ cotangentSupport b)
    {f : A} (hf : f ∈ CoordinateWeights.weightSpace b χ) (hfε : coordCounit H f = 0) :
    f ∈ RingHom.ker (coordCounit H) ^ 2 := by
  let g : augmentation H := ⟨f, hfε⟩
  have hg : g ∈ augmentationWeightSpace b χ := hf
  have hq : cotangentMk H g ∈ cotangentWeightSpace b χ := by
    rw [← (coordinateWeightDecomposition k H inferInstance S hS b).2.2.2 χ]
    exact Submodule.mem_map_of_mem hg
  rw [cotangentWeightSpace_eq_bot b hχ] at hq
  have h0 : (augmentationIdeal H).toCotangent ⟨f, hfε⟩ = 0 := (Submodule.mem_bot k).1 hq
  exact (Ideal.toCotangent_eq_zero _ _).1 h0

/-- Formal smoothness of the coordinate algebra of a smooth affine group. -/
theorem formallySmooth_coord [Smooth H.X.hom] : Algebra.FormallySmooth k A := by
  set D := CharacterUnits.Coord H
  have hsm : Smooth ((algSpec (CommRingCat.of k)).obj (op D)).hom := by
    have : IsIso (Lie.coordinateIso H).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Lie.coordinateIso H).hom))
    have h : Smooth ((Lie.coordinateIso H).hom.left ≫ H.X.hom) := inferInstance
    simpa only [Over.w] using h
  have := (DynamicSmooth.smooth_algSpec_iff D).1 hsm
  exact Algebra.Smooth.formallySmooth

/-- **Unipotence from a cotangent support without zero.** Let a split torus act on a smooth
connected affine group `H` so that the zero character does not occur in the augmentation
cotangent space. If the unit has weight zero and the counit kills every nonzero weight, then
`H` is unipotent. -/
theorem isUnipotent_of_zero_not_mem_cotangentSupport [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp H)
    (hsupp : (0 : characterLattice S) ∉ cotangentSupport b)
    (h1 : (1 : A) ∈ CoordinateWeights.weightSpace b 0)
    (hε : ∀ χ, χ ≠ 0 → ∀ f ∈ CoordinateWeights.weightSpace b χ, coordCounit H f = 0) :
    IsUnipotent H := by
  classical
  have := CharacterLatticeProof.isDomain_coord H
  have := isNoetherianRing_coord (G := H)
  have := formallySmooth_coord (H := H)
  set W := CoordinateWeights.weightSpace b
  have hW : DirectSum.IsInternal W := (coordinateWeightDecomposition k H inferInstance S hS b).1
  have hind := hW.submodule_iSupIndep
  have htop := hW.submodule_iSup_eq_top
  have hmul : ∀ χ ψ, W χ * W ψ ≤ W (χ + ψ) := fun χ ψ =>
    Submodule.mul_le.2 fun f hf g hg => mul_mem_weightSpace b hf hg
  obtain ⟨ν, hν⟩ := hS.exists_pairings_ne_zero (cotangentSupport b)
    (finite_cotangentSupport hS b) fun α hα h => hsupp (h ▸ hα)
  let w : characterLattice S →+ ℤ := ((latticePairing S).flip ν).toAddMonoidHom
  have hsq : ∀ χ, w χ = 0 → ∀ f ∈ W χ, coordCounit H f = 0 →
      f ∈ RingHom.ker (coordCounit H) ^ 2 := fun χ hχ f hf hfε =>
    mem_sq_of_not_mem_cotangentSupport hS b (fun h => hν χ h hχ) hf hfε
  refine isUnipotent_of_graded H (regrade W w) (isInternal_regrade hind htop)
    (fun d f hf => regrade_comul (Δ := (coordComul H).toLinearMap)
      (fun _ _ ha => coordComul_mem_iSup b hS ha) d hf)
    (le_regrade (map_zero w) h1) fun f hf hm => ?_
  exact exists_eq_smul_one_of_regrade hind htop h1 hmul (coordCounit H) hε (coordComul H)
    (lid_comp_coordCounit H) (rid_comp_coordCounit H) w hsq hf hm

/-- **Unipotence without zero Lie weights.** A smooth connected affine group with a split torus
action whose Lie eigenspace for the zero character vanishes is unipotent. -/
theorem isUnipotent_of_actionWeightSpace_zero_eq_bot [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp H)
    (h0 : RelativeRoot.actionWeightSpace b 0 = ⊥) : IsUnipotent H := by
  refine isUnipotent_of_zero_not_mem_cotangentSupport hS b ?_ (one_mem_weightSpace_zero b)
    fun χ hχ f hf => coordCounit_eq_zero b hS hχ hf
  rw [cotangentLieSupport k H inferInstance inferInstance S hS b]
  rintro ⟨X, hX, hXw, -⟩
  rw [h0] at hXw
  exact hX ((Submodule.mem_bot k).1 hXw)

end Group

end Langlands.GroupScheme.TorusUnipotence
