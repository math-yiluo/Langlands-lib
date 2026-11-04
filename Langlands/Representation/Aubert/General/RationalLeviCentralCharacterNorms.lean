import Langlands.Representation.Aubert.General.RationalLeviCentralTorusValuations
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Representation.Unitary.CentralUnitarizer

/-! # Moduli of characters on actual Levi-central torus points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The same subgroup is the inverse image of the ambient centralizer of
the literal Levi: torus points already belong to every standard Levi. -/
theorem leviCentralTorusPoints_eq_comap_centralizer
    (I : Finset (SimpleRoot i ν)) :
    leviCentralTorusPoints i ν I =
      (Subgroup.centralizer (levi i ν I : Set (rationalPoints G))).comap
        (rationalPoints.map i) := by
  ext t
  rw [mem_leviCentralTorusPoints_iff]
  constructor
  · rintro ⟨z, hz⟩ m hm
    change m * (t ≫ i.hom.hom) = (t ≫ i.hom.hom) * m
    rw [← hz]
    exact congrArg (fun x : levi i ν I => (x : rationalPoints G))
      (Subgroup.mem_center_iff.mp z.property ⟨m, hm⟩)
  · intro ht
    refine ⟨⟨⟨rationalPoints.map i t,
      torusPoints_le_levi i ν I ⟨t, rfl⟩⟩, ?_⟩, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro m
    apply Subtype.ext
    exact ht m m.property

/-- The natural homomorphism to the full abstract center of the literal Levi. -/
def leviCentralTorusPointToCenter (I : Finset (SimpleRoot i ν)) :
    leviCentralTorusPoints i ν I →* Subgroup.center (levi i ν I) where
  toFun t := ⟨⟨rationalPoints.map i (t : rationalPoints T.toGrp),
    torusPoints_le_levi i ν I ⟨(t : rationalPoints T.toGrp), rfl⟩⟩, by
      obtain ⟨z, hz⟩ := (mem_leviCentralTorusPoints_iff i ν I t).mp t.property
      have heq : (⟨rationalPoints.map i (t : rationalPoints T.toGrp),
          torusPoints_le_levi i ν I
            ⟨(t : rationalPoints T.toGrp), rfl⟩⟩ : levi i ν I) = z := by
        apply Subtype.ext
        exact hz.symm
      rw [heq]
      exact z.property⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (rationalPoints.map i)
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (rationalPoints.map i)
      (a : rationalPoints T.toGrp) (b : rationalPoints T.toGrp)

@[simp] theorem leviCentralTorusPointToCenter_val
    (I : Finset (SimpleRoot i ν)) (t : leviCentralTorusPoints i ν I) :
    (((leviCentralTorusPointToCenter i ν I t :
      Subgroup.center (levi i ν I)) : levi i ν I) : rationalPoints G) =
        rationalPoints.map i t := rfl

section Topology

variable [TopologicalSpace k] [IsAffine T.X.left]

local instance signsTorusTopology : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology k T.X
local instance signsAmbientTopology : TopologicalSpace (rationalPoints G) := pointTopology
local instance signsAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)]

theorem isClosed_leviCentralTorusPoints (I : Finset (SimpleRoot i ν)) :
    IsClosed (leviCentralTorusPoints i ν I : Set (rationalPoints T.toGrp)) := by
  rw [leviCentralTorusPoints_eq_comap_centralizer]
  exact (Set.isClosed_centralizer _).preimage
    (continuous_rationalPointMap k i.hom.hom)

omit [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)] in
theorem continuous_leviCentralTorusPointToCenter (I : Finset (SimpleRoot i ν)) :
    Continuous (leviCentralTorusPointToCenter i ν I) := by
  exact (((continuous_rationalPointMap k i.hom.hom).comp
    continuous_subtype_val).subtype_mk _).subtype_mk _

omit [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)] in
/-- A central character restricts to a smooth character of the actual central
torus-point subgroup. -/
theorem isOpen_ker_leviCentralTorusCharacter
    (I : Finset (SimpleRoot i ν))
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I)))) :
    IsOpen ((χ.comp (leviCentralTorusPointToCenter i ν I)).ker :
      Set (leviCentralTorusPoints i ν I)) :=
  hχ.preimage (continuous_leviCentralTorusPointToCenter i ν I)

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- The modulus of a smooth full-center character is one on the compact
norm-kernel part of the actual Levi-central torus subgroup. -/
theorem leviCentralTorusCharacter_norm_eq_one_of_mem_normKernel
    (hT : IsSplitTorus T.toGrp) (I : Finset (SimpleRoot i ν))
    (χ : Subgroup.center (levi i ν I) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (levi i ν I))))
    (t : leviCentralTorusPoints i ν I)
    (ht : (t : rationalPoints T.toGrp) ∈ Plancherel.rationalCommonNormKernel T.toGrp) :
    ‖(χ (leviCentralTorusPointToCenter i ν I t) : ℂ)‖ = 1 := by
  let : Smooth T.X.hom := hT.smooth
  let : IsTopologicalGroup (rationalPoints T.toGrp) :=
    rationalPoint_isTopologicalGroup k T.toGrp
  let H := leviCentralTorusPoints i ν I
  let K := (Plancherel.rationalCommonNormKernel T.toGrp).subgroupOf H
  have hK : IsCompact (K : Set H) := by
    apply (Topology.IsEmbedding.isCompact_iff
      (f := fun t : H => (t : rationalPoints T.toGrp))
      Topology.IsEmbedding.subtypeVal).mpr
    have heq : Subtype.val '' (K : Set H) =
        (H : Set (rationalPoints T.toGrp)) ∩
          (Plancherel.rationalCommonNormKernel T.toGrp : Set (rationalPoints T.toGrp)) := by
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hxH, hxK⟩
        exact ⟨⟨x, hxH⟩, hxK, rfl⟩
    rw [heq, Set.inter_comm]
    exact (Plancherel.SplitTorus.isCompact_commonNormKernel hT).inter_right
      (isClosed_leviCentralTorusPoints i ν I)
  have hone := PositiveCharacter.eq_one_on_compact
    (PositiveCharacter.normCharacter (χ.comp (leviCentralTorusPointToCenter i ν I)))
    (PositiveCharacter.isOpen_ker_normCharacter _
      (isOpen_ker_leviCentralTorusCharacter i ν I χ hχ)) K hK ⟨t, ht⟩
  exact congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hone

end Topology

end Langlands.Aubert.General.RationalPointFamily
