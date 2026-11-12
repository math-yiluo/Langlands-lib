import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.Representation.Induction.OpenAdjunction
import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisStatement
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Mathlib.RepresentationTheory.Invariants

/-! # Depth-zero inflation and compact induction for supplied KP models

A representation of the residue-field points `Gred(f)` of the supplied quotient is
inflated to `G^0(R)` through `parahoricReduction`. Vectors fixed by the reduction kernel
carry an action of `Gred(f)`, and inflation is left adjoint to these invariants on
intertwining maps. When the congruence subgroup is open, the inflation is smooth and its
compact induction to `G(K)` satisfies the depth-zero Frobenius reciprocity
`Hom_G(c-Ind infl σ, π) ≃ Hom_{Gred(f)}(σ, π^{ker})` for open `G^0(R)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u uk

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

section Local

variable [IsLocalRing R]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
variable {k : Type uk} [CommRing k]
  {V : Type u} [AddCommGroup V] [Module k V] {W : Type u} [AddCommGroup W] [Module k W]

/-- Inflation of a representation of `Gred(f)` to `G^0(R)` through the reduction map. -/
def inflation (σ : Representation k (rationalPoints Q.quotient) V) :
    Representation k D.neutral.integralPoints V :=
  σ.comp Q.parahoricReduction

@[simp]
theorem inflation_apply (σ : Representation k (rationalPoints Q.quotient) V)
    (g : D.neutral.integralPoints) : Q.inflation σ g = σ (Q.parahoricReduction g) :=
  rfl

/-- The congruence subgroup of the neutral model lies in the reduction kernel. -/
theorem congruenceSubgroup_subgroupOf_le_ker :
    D.neutral.congruenceSubgroup.subgroupOf D.neutral.integralPoints ≤
      Q.parahoricReduction.ker := by
  intro g hg
  obtain ⟨x, hx, hxg⟩ := (IntegralModel.mem_congruenceSubgroup _ _).mp hg
  have hg' : g = D.neutralSectionsEquiv x := Subtype.ext hxg.symm
  rw [MonoidHom.mem_ker, hg', parahoricReduction_neutralSectionsEquiv, reductiveReduction,
    MonoidHom.comp_apply, hx, map_one]

/-- Elements of the reduction kernel act trivially on an inflation. -/
theorem inflation_ker_apply (σ : Representation k (rationalPoints Q.quotient) V)
    {g : D.neutral.integralPoints} (hg : g ∈ Q.parahoricReduction.ker) (v : V) :
    Q.inflation σ g v = v := by
  rw [inflation_apply, MonoidHom.mem_ker.mp hg, map_one, Module.End.one_apply]

end SpecialFibreQuotientData

end Local

section Henselian

variable [HenselianLocalRing R] [PerfectField (IsLocalRing.ResidueField R)]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
variable {k : Type uk} [CommRing k]
  {V : Type u} [AddCommGroup V] [Module k V] {W : Type u} [AddCommGroup W] [Module k W]
/-- The inverse of `depthZeroQuotientEquiv` sends a reduction to its coset. -/
theorem depthZeroQuotientEquiv_symm_parahoricReduction
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection)
    (g : D.neutral.integralPoints) :
    (Q.depthZeroQuotientEquiv hrad hQ).symm (Q.parahoricReduction g) =
      (g : D.neutral.integralPoints ⧸ Q.parahoricReduction.ker) := by
  rw [MulEquiv.symm_apply_eq]
  rfl

/-- `Gred(f)` acting on the vectors of a `G^0(R)`-representation fixed by the reduction
kernel, through `depthZeroQuotientEquiv`. -/
def kernelInvariants (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection)
    (ρ : Representation k D.neutral.integralPoints W) :
    Representation k (rationalPoints Q.quotient)
      (Representation.invariants (ρ.comp Q.parahoricReduction.ker.subtype)) :=
  (ρ.quotientToInvariants Q.parahoricReduction.ker).comp
    (Q.depthZeroQuotientEquiv hrad hQ).symm.toMonoidHom

@[simp]
theorem kernelInvariants_parahoricReduction_apply
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection)
    (ρ : Representation k D.neutral.integralPoints W) (g : D.neutral.integralPoints)
    (w : Representation.invariants (ρ.comp Q.parahoricReduction.ker.subtype)) :
    ((Q.kernelInvariants hrad hQ ρ (Q.parahoricReduction g) w : _) : W) = ρ g w := by
  simp only [kernelInvariants, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Q.depthZeroQuotientEquiv_symm_parahoricReduction hrad hQ]
  rfl

/-- Inflation is left adjoint to kernel invariants on intertwining maps:
`Hom_{G^0(R)}(infl σ, ρ) ≃ Hom_{Gred(f)}(σ, ρ^{ker})`. -/
def inflationHomEquiv (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection)
    (σ : Representation k (rationalPoints Q.quotient) V)
    (ρ : Representation k D.neutral.integralPoints W) :
    (Q.inflation σ).IntertwiningMap ρ ≃
      σ.IntertwiningMap (Q.kernelInvariants hrad hQ ρ) where
  toFun T :=
    { toLinearMap := T.toLinearMap.codRestrict _ fun v => by
        rw [Representation.mem_invariants]
        rintro ⟨x, hx⟩
        change ρ x (T v) = T v
        rw [← T.isIntertwining, Q.inflation_ker_apply σ hx]
      isIntertwining' := fun y => LinearMap.ext fun v => by
        obtain ⟨g, rfl⟩ := Q.parahoricReduction_surjective hrad hQ y
        apply Subtype.ext
        change T (Q.inflation σ g v) = _
        rw [LinearMap.comp_apply, Q.kernelInvariants_parahoricReduction_apply hrad hQ]
        exact LinearMap.congr_fun (T.isIntertwining' g) v }
  invFun S :=
    { toLinearMap := (Submodule.subtype _).comp S.toLinearMap
      isIntertwining' := fun g => LinearMap.ext fun v => by
        change ((S (σ (Q.parahoricReduction g) v) : _) : W) = ρ g (S v)
        rw [S.isIntertwining, Q.kernelInvariants_parahoricReduction_apply hrad hQ] }
  left_inv T := by
    ext v
    rfl
  right_inv S := by
    ext v
    rfl

end SpecialFibreQuotientData

end Henselian

section Topology

variable [IsLocalRing R] [TopologicalSpace (rationalPoints G)]
  [IsTopologicalGroup (rationalPoints G)]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
variable {k : Type uk} [CommRing k]
  {V : Type u} [AddCommGroup V] [Module k V]
/-- If the congruence subgroup is open in `G(K)`, the reduction kernel is open in
`G^0(R)`. -/
theorem isOpen_ker_parahoricReduction
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G))) :
    IsOpen (Q.parahoricReduction.ker : Set D.neutral.integralPoints) :=
  Subgroup.isOpen_mono Q.congruenceSubgroup_subgroupOf_le_ker
    (continuous_subtype_val.isOpen_preimage _ hC)

/-- The reduction kernel as an open subgroup of `G^0(R)`. -/
def kerOpenSubgroup (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G))) :
    OpenSubgroup D.neutral.integralPoints :=
  ⟨Q.parahoricReduction.ker, Q.isOpen_ker_parahoricReduction hC⟩

/-- Inflations are smooth when the congruence subgroup is open. -/
theorem isSmooth_inflation (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V) :
    IsSmooth (Q.inflation σ) := by
  intro v
  refine ⟨Q.kerOpenSubgroup hC, ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  rintro ⟨x, hx⟩
  exact Q.inflation_ker_apply σ hx v

/-- The inflation as a bundled smooth representation of `G^0(R)`. -/
abbrev inflationSmoothRep (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V) :
    SmoothRep.{uk, u, u} k D.neutral.integralPoints :=
  SmoothRep.of (Q.inflation σ) (Q.isSmooth_inflation hC σ)

/-- The depth-zero compact induction `c-Ind_{G^0(R)}^{G(K)} infl σ`. -/
abbrev depthZeroInduction (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V) :
    SmoothRep.{uk, u, u} k (rationalPoints G) :=
  (Induction.smoothCompactInduction k D.neutral.integralPoints).obj
    (Q.inflationSmoothRep hC σ)

end SpecialFibreQuotientData

end Topology

section HenselianTopology

variable [HenselianLocalRing R] [PerfectField (IsLocalRing.ResidueField R)]
  [TopologicalSpace (rationalPoints G)] [IsTopologicalGroup (rationalPoints G)]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
variable {k : Type uk} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]
/-- Depth-zero Frobenius reciprocity: for open `G^0(R)` and open congruence subgroup,
`Hom_{G(K)}(c-Ind infl σ, π) ≃ Hom_{Gred(f)}(σ, π^{ker})`, where `π^{ker}` is the space of
vectors fixed by the reduction kernel `G(K)^{0+} ∩ G^0(R)`. -/
def depthZeroInductionHomEquiv (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection)
    (hH : IsOpen (D.neutral.integralPoints : Set (rationalPoints G)))
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V)
    (B : SmoothRep.{uk, u, u} k (rationalPoints G)) :
    (Q.depthZeroInduction hC σ ⟶ B) ≃
      σ.IntertwiningMap
        (Q.kernelInvariants hrad hQ (B.representation.comp D.neutral.integralPoints.subtype)) :=
  (Induction.compactInductionHomEquiv D.neutral.integralPoints hH
      (Q.inflationSmoothRep hC σ) B).trans <|
    ({ toFun := SmoothRep.hom
       invFun := fun f => SmoothRep.ofHom (A := Q.inflationSmoothRep hC σ)
         (B := (Induction.smoothRestriction k D.neutral.integralPoints).obj B) f
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
      (Q.inflationSmoothRep hC σ ⟶
          (Induction.smoothRestriction k D.neutral.integralPoints).obj B) ≃
        (Q.inflation σ).IntertwiningMap
          (B.representation.comp D.neutral.integralPoints.subtype)).trans
      (Q.inflationHomEquiv hrad hQ σ _)

end SpecialFibreQuotientData

end HenselianTopology

section LocalField

open Langlands.AlgebraicGeometry.PointTopology
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The valuation ring of a nonarchimedean local field is a Henselian local ring. -/
theorem henselianLocalRing_integer : HenselianLocalRing 𝒪[F] := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  refine { is_henselian := ?_ }
  intro f hf a₀ hroot hder
  exact HenselianRing.is_henselian f hf a₀ hroot
    (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[F])))

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- Under the congruence-basis statement, `G^0(𝒪)` is open in `G(F)`. -/
theorem isOpen_integralPoints_of_congruenceBasis
    (hbasis : LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement.{u})
    (D : RelativeComponentModelData 𝒪[F] F G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsOpen (D.neutral.integralPoints : Set (rationalPoints G)) :=
  (hbasis F G D.neutral).2.1

/-- Under the congruence-basis statement, the level-one congruence subgroup of the neutral
model is open in `G(F)`. -/
theorem isOpen_congruenceSubgroup_of_congruenceBasis
    (hbasis : LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement.{u})
    (D : RelativeComponentModelData 𝒪[F] F G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)) := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have h := ((hbasis F G D.neutral).2.2.1 1).2.1
  rwa [IntegralModel.congruenceSubgroupAt_one] at h

variable [LocallyOfFiniteType G.X.hom]
variable {k : Type uk} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V]

/-- Depth-zero Frobenius reciprocity for `G(F)` with its canonical topology, assuming the
congruence-basis statement: `Hom_{G(F)}(c-Ind infl σ, π) ≃ Hom_{Gred(𝓀)}(σ, π^{ker})`. -/
def localFieldDepthZeroInductionHomEquiv
    (hbasis : LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement.{u})
    {D : RelativeComponentModelData 𝒪[F] F G} (Q : SpecialFibreQuotientData D)
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection)
    (σ : Representation k (rationalPoints Q.quotient) V) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    letI : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
    ∀ B : SmoothRep.{uk, u, u} k (rationalPoints G),
      (Q.depthZeroInduction (isOpen_congruenceSubgroup_of_congruenceBasis hbasis D) σ ⟶ B) ≃
        σ.IntertwiningMap (Q.kernelInvariants hrad hQ
          (B.representation.comp D.neutral.integralPoints.subtype)) :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  letI : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer
  fun B => Q.depthZeroInductionHomEquiv hrad hQ
    (isOpen_integralPoints_of_congruenceBasis hbasis D)
    (isOpen_congruenceSubgroup_of_congruenceBasis hbasis D) σ B

end LocalField

end Langlands.BruhatTits.IntegralModels
