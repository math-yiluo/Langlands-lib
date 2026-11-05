import Langlands.Representation.CuspidalSupport.RationalNormKernelCompressionLevel
import Langlands.Representation.Plancherel.RationalNormKernelResidualCover
import Langlands.Representation.Hecke.FiniteResidualSandwich
import Langlands.Representation.CompactCoefficient.FiniteStratumUniformSupport
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-! # Common support from an actual norm-kernel level and central Cartan charts -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry Topology MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance normKernelSupportSandwichPointTopology :
    TopologicalSpace (RationalPoint F G.X) := pointTopology

variable [Fintype (SimpleRoot i ν)]

/-- Ambient central charts retaining the exact prescribed norm-kernel orthant.
The chart identity is required only on the actual norm kernel. -/
structure NormKernelCentralCartanCover (d : NormKernelFundamentalCocharacters i ν)
    (K0 : Subgroup (RationalPoint F G.X)) where
  residual : Set (RationalPoint F G.X)
  finite : residual.Finite
  cover : ∀ g : Plancherel.rationalCommonNormKernel G,
    ∃ k₁ ∈ K0, ∃ k₂ ∈ K0, ∃ f ∈ residual,
      ∃ n : SimpleRoot i ν → ℕ,
      ∃ z ∈ Subgroup.center (RationalPoint F G.X),
        (g : RationalPoint F G.X) =
          k₁ * ((d.orthantHom (.ofAdd n) : RationalPoint F G.X) * f) * k₂ * z

namespace NormKernelCompressionLevel

variable {d : NormKernelFundamentalCocharacters i ν}
    {K0 : Subgroup (RationalPoint F G.X)}
    {U : OpenSubgroup (Plancherel.rationalCommonNormKernel G)}
    (L : NormKernelCompressionLevel d K0 U)

/-- Normalize the image of the actual kernel level using its retained
normalizer and containment of compact ambient subgroups in the norm kernel. -/
theorem ambient_normalized (hG : IsConnectedReductive G)
    (hK0 : IsCompact (K0 : Set (RationalPoint F G.X))) :
    K0 ≤ Subgroup.normalizer
      (L.level.toSubgroup.map (Plancherel.rationalCommonNormKernel G).subtype :
        Set (RationalPoint F G.X)) := by
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := Plancherel.rationalCommonNormKernel G
  have hKH : K0 ≤ H := Plancherel.compactSubgroup_le_rationalCommonNormKernel G K0 hK0
  intro k hk
  exact Subgroup.le_normalizer_map H.subtype
    ⟨⟨k, hKH hk⟩, L.normalized hk, rfl⟩

variable [T2Space (RationalPoint F G.X)]
    [MeasurableSpace (Plancherel.rationalCommonNormKernel G)]
    [BorelSpace (Plancherel.rationalCommonNormKernel G)]

/-- The compact central part of the actual norm kernel enlarges the retained
normalizer, and finite residual descent gives genuine kernel sandwich data. -/
theorem nonempty_sandwich_of_centralCartanCover
    (hG : IsConnectedReductive G)
    (hK0 : IsCompact (K0 : Set (RationalPoint F G.X)))
    (C : NormKernelCentralCartanCover d K0)
    (mu : Measure (Plancherel.rationalCommonNormKernel G)) [mu.IsHaarMeasure] :
    letI := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    let : IsTopologicalGroup (RationalPoint F G.X) :=
      rationalPoint_isTopologicalGroup F G
    Nonempty (Hecke.FixedLevelSandwich mu L.level L.compact) := by
  classical
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := Plancherel.rationalCommonNormKernel G
  let : IsTopologicalGroup (RationalPoint F G.X) :=
    rationalPoint_isTopologicalGroup F G
  let K := L.level.toSubgroup.map H.subtype
  obtain ⟨Γ, hΓc, -, hΓ, R, hR, hcover⟩ :=
    Plancherel.exists_rationalNormKernel_residual_cover G hG K K0 hK0
      (L.ambient_normalized hG hK0)
      (fun n => d.orthantHom (.ofAdd n)) C.residual C.finite C.cover
  have hcomap : K.comap H.subtype = L.level.toSubgroup :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective L.level.toSubgroup
  rw [hcomap] at hΓ
  exact Hecke.nonempty_fixedLevelSandwich_of_residual_iwahoriCartan
    L.level L.compact mu (normKernelUnipotent i ν ∅) (normKernelLevi i ν ∅)
      (normKernelStandardOpposite (i := i) (ν := ν) ∅)
      L.factor d.orthantHom L.positive L.forward_levi Γ hΓc hΓ R hR hcover

/-- The actual Haar Hecke sandwich selected from the supplied common level
and central cover; no representation is involved in this choice. -/
def sandwichOfCentralCartanCover (hG : IsConnectedReductive G)
    (hK0 : IsCompact (K0 : Set (RationalPoint F G.X)))
    (C : NormKernelCentralCartanCover d K0)
    (mu : Measure (Plancherel.rationalCommonNormKernel G)) [mu.IsHaarMeasure] :
    letI := hG.smooth
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsTopologicalGroup (RationalPoint F G.X) :=
      rationalPoint_isTopologicalGroup F G
    Hecke.FixedLevelSandwich mu L.level L.compact := by
  exact Classical.choice (L.nonempty_sandwich_of_centralCartanCover hG hK0 C mu)

include L in
/-- Conditional support at the prescribed level is uniform over every actual
compact irreducible class in an independent representation-carrier universe. -/
theorem hasUniformSupport_of_centralCartanCover (hG : IsConnectedReductive G)
    (hK0 : IsCompact (K0 : Set (RationalPoint F G.X)))
    (C : NormKernelCentralCartanCover d K0)
    (mu : Measure (Plancherel.rationalCommonNormKernel G)) [mu.IsHaarMeasure] :
    CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport.{uF, uV}
      U.toSubgroup := by
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsTopologicalGroup (RationalPoint F G.X) :=
    rationalPoint_isTopologicalGroup F G
  obtain ⟨S, hS, hbound⟩ :=
    CompactCoefficientClass.hasUniformFixedLevelCoefficientSupport_of_sandwich
      mu L.level L.compact (L.sandwichOfCentralCartanCover hG hK0 C mu)
  refine ⟨S, hS, fun D v hv ℓ hℓ => ?_⟩
  exact hbound D v (fixedVectors_antitone D.obj.representation L.le_prescribed hv)
    ℓ (fun k hk w => hℓ k (L.le_prescribed hk) w)

end NormKernelCompressionLevel

end Langlands.Aubert.General.RationalPointFamily
