import Langlands.LocalFactor.NonabelianSystemFieldTransportExtension
import Langlands.Global.Factors.HenniartCompositeFactorWeil

/-!
# Exact virtual groups along an isomorphism of p-adic fields

For `g : F ≅ E` over `ℚ_p` and a finite intermediate field `L` of `F̄`, restriction
along `W_E(σ(L)) ≅ W_F(L)` followed by the carrier-universe change is a map of exact
virtual groups `Virtual F L → Virtual E σ(L)`. It preserves degree, character
classes, the spectral twist and common-closure induction.
-/

noncomputable section

universe u₁ u₂ uV uG uA uB

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The carrier-universe change preserves degree. -/
theorem degree_universeMap (x : Continuous.{uG, uA} G) :
    degree (fun A : FiniteRepresentation.{0, uG, uB} ℂ G => A.IsContinuous)
        (universeMap x : Continuous.{uG, uB} G) =
      degree (fun A : FiniteRepresentation.{0, uG, uA} ℂ G => A.IsContinuous) x := by
  have hc : (degree (fun A : FiniteRepresentation.{0, uG, uB} ℂ G => A.IsContinuous)).comp
      (universeMap : Continuous.{uG, uA} G →ₗ[ℤ] Continuous.{uG, uB} G) =
      degree (fun A : FiniteRepresentation.{0, uG, uA} ℂ G => A.IsContinuous) := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change degree _ (universeMap (ofRepresentation _ A)) = degree _ (ofRepresentation _ A)
      rw [universeMap_ofRepresentation_of_equiv A ⟨universeModel A.val,
          (isContinuous_iff_of_equiv (universeModelEquiv A.val)).mp A.property⟩
          (universeModelEquiv A.val), degree_ofRepresentation, degree_ofRepresentation]
      exact_mod_cast (rank_eq_of_equiv (universeModelEquiv A.val)).symm
  exact LinearMap.congr_fun hc x

/-- The carrier-universe change commutes with twisting by a continuous character. -/
theorem universeMap_continuousTwist (χ : G →ₜ* ℂˣ) (x : Continuous.{uG, uA} G) :
    (universeMap (continuousTwist χ x) : Continuous.{uG, uB} G) =
      continuousTwist χ (universeMap x) := by
  have hc : (universeMap : Continuous.{uG, uA} G →ₗ[ℤ] Continuous.{uG, uB} G).comp
      (continuousTwist χ).toLinearMap =
      (continuousTwist χ).toLinearMap.comp universeMap := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change universeMap (twist χ.toMonoidHom _ _ _ (ofRepresentation _ A)) =
        twist χ.toMonoidHom _ _ _ (universeMap (ofRepresentation _ A))
      rw [universeMap_ofRepresentation_of_equiv A ⟨universeModel A.val,
          (isContinuous_iff_of_equiv (universeModelEquiv A.val)).mp A.property⟩
          (universeModelEquiv A.val), twist_ofRepresentation, twist_ofRepresentation]
      exact universeMap_ofRepresentation_of_equiv _ _
        (Langlands.twistEquiv χ.toMonoidHom (universeModelEquiv A.val))
  exact LinearMap.congr_fun hc x

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.LocalFactor.NonabelianSystem.FieldTransport

open LocalClassField Weil.Local CommonClosure VirtualRepresentation FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u₁} p) (E : PadicField.{u₂} p)
  (g : F.Carrier ≃ₐ[Padic p] E.Carrier)

theorem localDegree_weilEquiv (w : localWeilGroup E) :
    localDegree F (weilEquiv F E g w) = localDegree E w := by
  rw [extensionWeilEquiv_apply, localDegree_extensionWeilMap, extensionResidueDegree_algEquiv,
    pow_one]

/-- Restriction along `W_E(σ(L)) ≅ W_F(L)`, followed by the carrier-universe change. -/
def virtualMap (L : Extension F) :
    Virtual.{u₁, uV} F L →ₗ[ℤ] Virtual.{u₂, uV} E (mapExtension F E g L) :=
  ExactGrothendieckGroup.universeMap.comp
    (ExactGrothendieckGroup.continuousRestrict (subgroupWeilEquiv F E g L : _ →ₜ* _))

theorem virtualMap_apply (L : Extension F) (x : Virtual.{u₁, uV} F L) :
    virtualMap F E g L x = ExactGrothendieckGroup.universeMap
      (ExactGrothendieckGroup.continuousRestrict (subgroupWeilEquiv F E g L : _ →ₜ* _) x) :=
  rfl

/-- On a generator, the map is the class of any representation equivalent to the
restriction. -/
theorem virtualMap_ofRepresentation (L : Extension F)
    (A : {A : FiniteRepresentation.{0, u₁, max u₁ uV} ℂ (weilSubgroup F L) // A.IsContinuous})
    (B : {B : FiniteRepresentation.{0, u₂, max u₂ uV} ℂ (weilSubgroup E (mapExtension F E g L)) //
      B.IsContinuous})
    (e : FiniteRepresentation.Equiv
      (restrict (subgroupWeilEquiv F E g L : _ →ₜ* _).toMonoidHom A.val) B.val) :
    virtualMap F E g L (ExactGrothendieckGroup.ofRepresentation _ A) =
      ExactGrothendieckGroup.ofRepresentation _ B := by
  rw [virtualMap_apply, ExactGrothendieckGroup.continuousRestrict,
    ExactGrothendieckGroup.restrict_ofRepresentation]
  exact ExactGrothendieckGroup.universeMap_ofRepresentation_of_equiv _ _ e

theorem degree_virtualMap (L : Extension F) (x : Virtual.{u₁, uV} F L) :
    degree E (mapExtension F E g L) (virtualMap F E g L x) = degree F L x := by
  rw [virtualMap_apply]
  exact (ExactGrothendieckGroup.degree_universeMap _).trans
    (ExactGrothendieckGroup.degree_continuousRestrict _ x)

/-- The map on characters: precomposition with `W_E(σ(L)) ≅ W_F(L)`. -/
theorem virtualMap_characterClass (L : Extension F) (χ : weilSubgroup F L →ₜ* ℂˣ) :
    virtualMap F E g L (ExactGrothendieckGroup.characterClass χ) =
      ExactGrothendieckGroup.characterClass (χ.comp (subgroupWeilEquiv F E g L : _ →ₜ* _)) := by
  rw [virtualMap_apply, ExactGrothendieckGroup.continuousRestrict_characterClass,
    ExactGrothendieckGroup.universeMap_characterClass]

/-- The map commutes with twisting, with the character precomposed. -/
theorem virtualMap_continuousTwist (L : Extension F) (χ : weilSubgroup F L →ₜ* ℂˣ)
    (x : Virtual.{u₁, uV} F L) :
    virtualMap F E g L (ExactGrothendieckGroup.continuousTwist χ x) =
      ExactGrothendieckGroup.continuousTwist (χ.comp (subgroupWeilEquiv F E g L : _ →ₜ* _))
        (virtualMap F E g L x) := by
  rw [virtualMap_apply, ExactGrothendieckGroup.continuousRestrict_continuousTwist,
    ExactGrothendieckGroup.universeMap_continuousTwist]
  rfl

include g in
theorem baseCardinality_eq : CommonClosureSpectral.baseCardinality E =
    CommonClosureSpectral.baseCardinality F := by
  unfold CommonClosureSpectral.baseCardinality
  exact_mod_cast PadicField.CanonicalTransport.residueCardinality_eq F E g

theorem character_comp (L : Extension F) (s : ℂ) :
    (CommonClosureSpectral.character F L s).comp (subgroupWeilEquiv F E g L : _ →ₜ* _) =
      CommonClosureSpectral.character E (mapExtension F E g L) s := by
  ext w
  change (CommonClosureSpectral.character F L s (subgroupWeilEquiv F E g L w) : ℂ) =
    (CommonClosureSpectral.character E (mapExtension F E g L) s w : ℂ)
  rw [CommonClosureSpectral.character_apply, CommonClosureSpectral.character_apply,
    subgroupWeilEquiv_coe, localDegree_weilEquiv, baseCardinality_eq F E g]

/-- The map commutes with the spectral twist. -/
theorem virtualMap_virtualTwist (L : Extension F) (s : ℂ) (x : Virtual.{u₁, uV} F L) :
    virtualMap F E g L (CommonClosureSpectral.virtualTwist F L s x) =
      CommonClosureSpectral.virtualTwist E (mapExtension F E g L) s (virtualMap F E g L x) := by
  change virtualMap F E g L (ExactGrothendieckGroup.continuousTwist
      (CommonClosureSpectral.character F L s) x) =
    ExactGrothendieckGroup.continuousTwist
      (CommonClosureSpectral.character E (mapExtension F E g L) s) (virtualMap F E g L x)
  rw [virtualMap_continuousTwist, character_comp]

theorem subgroupWeilEquiv_mem_subgroupOf_iff (M L : Extension F)
    (w : weilSubgroup E (mapExtension F E g M)) :
    subgroupWeilEquiv F E g M w ∈ (weilSubgroup F L).subgroupOf (weilSubgroup F M) ↔
      w ∈ (weilSubgroup E (mapExtension F E g L)).subgroupOf
        (weilSubgroup E (mapExtension F E g M)) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, subgroupWeilEquiv_coe]
  exact weilEquiv_mem_iff F E g L (w : localWeilGroup E)

/-- `W_E(σ(L)) ≅ W_F(L)` on the nested subgroups, inside `W_E(σ(M)) ≅ W_F(M)`. -/
def nestedSubgroupHom (M L : Extension F) :
    (weilSubgroup E (mapExtension F E g L)).subgroupOf (weilSubgroup E (mapExtension F E g M)) →*
      (weilSubgroup F L).subgroupOf (weilSubgroup F M) :=
  ((subgroupWeilEquiv F E g M).toMulEquiv.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _
    (fun s => (subgroupWeilEquiv_mem_subgroupOf_iff F E g M L s).mpr s.property)

theorem nestedSubgroupHom_coe (M L : Extension F)
    (s : (weilSubgroup E (mapExtension F E g L)).subgroupOf
      (weilSubgroup E (mapExtension F E g M))) :
    (nestedSubgroupHom F E g M L s : weilSubgroup F M) =
      (subgroupWeilEquiv F E g M).toMulEquiv s := rfl

theorem nestedWeilEquiv_nestedSubgroupHom {M L : Extension F} (h : M.field ≤ L.field)
    (s : (weilSubgroup E (mapExtension F E g L)).subgroupOf
      (weilSubgroup E (mapExtension F E g M))) :
    (nestedWeilEquiv F M L h : _ →ₜ* weilSubgroup F L) (nestedSubgroupHom F E g M L s) =
      (subgroupWeilEquiv F E g L : _ →ₜ* weilSubgroup F L)
        ((nestedWeilEquiv E (mapExtension F E g M) (mapExtension F E g L)
          (mapExtension_mono F E g h) : _ →ₜ* weilSubgroup E (mapExtension F E g L)) s) := rfl

/-- Restriction along the nested maps, in either order around the square. -/
def nestedRestrictEquiv {M L : Extension F} (h : M.field ≤ L.field)
    (A : FiniteRepresentation.{0, u₁, max u₁ uV} ℂ (weilSubgroup F L)) :
    FiniteRepresentation.Equiv
      (restrict (nestedSubgroupHom F E g M L)
        (restrict ((nestedWeilEquiv F M L h : (weilSubgroup F L).subgroupOf (weilSubgroup F M) →ₜ*
          weilSubgroup F L)).toMonoidHom A))
      (restrict ((nestedWeilEquiv E (mapExtension F E g M) (mapExtension F E g L)
        (mapExtension_mono F E g h) : (weilSubgroup E (mapExtension F E g L)).subgroupOf
          (weilSubgroup E (mapExtension F E g M)) →ₜ* weilSubgroup E (mapExtension F E g L))).toMonoidHom
        (restrict ((subgroupWeilEquiv F E g L : weilSubgroup E (mapExtension F E g L) →ₜ*
          weilSubgroup F L)).toMonoidHom A)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' _ := rfl

/-- Restriction to `W_E(σ(M))` of a representation induced from `W_F(L)` is induced
from `W_E(σ(L))`. -/
def restrictInduceNestedEquiv (M L : Extension F)
    (B : FiniteRepresentation.{0, u₁, max u₁ uV} ℂ
      ((weilSubgroup F L).subgroupOf (weilSubgroup F M))) :
    FiniteRepresentation.Equiv
      (restrict ((subgroupWeilEquiv F E g M : weilSubgroup E (mapExtension F E g M) →ₜ*
          weilSubgroup F M)).toMonoidHom
        (induce ((weilSubgroup F L).subgroupOf (weilSubgroup F M)) B))
      (induce ((weilSubgroup E (mapExtension F E g L)).subgroupOf
          (weilSubgroup E (mapExtension F E g M)))
        (restrict (nestedSubgroupHom F E g M L) B)) :=
  restrictInduceEquiv (subgroupWeilEquiv F E g M).toMulEquiv _ _
    (nestedSubgroupHom F E g M L) (fun _ => rfl)
    (fun w hw => (subgroupWeilEquiv_mem_subgroupOf_iff F E g M L w).mp hw) B

/-- Restriction to `W_E(σ(M))` of a representation induced from `W_F(L)` is induced from
`W_E(σ(L))`, for any model of the restriction to `W_E(σ(L))`. -/
def restrictInducedEquiv {M L : Extension F} (h : M.field ≤ L.field)
    (A : FiniteRepresentation.ContinuousObjects.{u₁, max u₁ uV} (weilSubgroup F L))
    (A' : FiniteRepresentation.ContinuousObjects.{u₂, max u₂ uV}
      (weilSubgroup E (mapExtension F E g L)))
    (e : FiniteRepresentation.Equiv
      (restrict (subgroupWeilEquiv F E g L : _ →ₜ* _).toMonoidHom A.val) A'.val) :
    FiniteRepresentation.Equiv
      (restrict (subgroupWeilEquiv F E g M : _ →ₜ* _).toMonoidHom
        (inducedRepresentation F M L h A).val)
      (inducedRepresentation E (mapExtension F E g M) (mapExtension F E g L)
        (mapExtension_mono F E g h) A').val :=
  (restrictInduceNestedEquiv F E g M L _).trans
    (induceEquivOfEquiv _ ((nestedRestrictEquiv F E g h A.val).trans (restrictEquivOfEquiv _ e)))

/-- The map commutes with common-closure induction. -/
theorem virtualMap_induce {M L : Extension F} (h : M.field ≤ L.field)
    (x : Virtual.{u₁, uV} F L) :
    virtualMap F E g M (induce F M L h x) =
      induce E (mapExtension F E g M) (mapExtension F E g L) (mapExtension_mono F E g h)
        (virtualMap F E g L x) := by
  have hc : (virtualMap F E g M).comp (induce F M L h) =
      (induce E (mapExtension F E g M) (mapExtension F E g L)
        (mapExtension_mono F E g h)).comp (virtualMap F E g L) := by
    apply ExactGrothendieckGroup.hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change virtualMap F E g M (induce F M L h (ExactGrothendieckGroup.ofRepresentation _ A)) =
        induce E (mapExtension F E g M) (mapExtension F E g L) (mapExtension_mono F E g h)
          (virtualMap F E g L (ExactGrothendieckGroup.ofRepresentation _ A))
      let R : FiniteRepresentation.ContinuousObjects.{u₂, max u₁ uV}
          (weilSubgroup E (mapExtension F E g L)) :=
        FiniteRepresentation.continuousRestrict (subgroupWeilEquiv F E g L : _ →ₜ* _).toMonoidHom
          (subgroupWeilEquiv F E g L).continuous A
      let A' : FiniteRepresentation.ContinuousObjects.{u₂, max u₂ uV}
          (weilSubgroup E (mapExtension F E g L)) :=
        ⟨universeModel R.val, (isContinuous_iff_of_equiv (universeModelEquiv R.val)).mp R.property⟩
      have hA : virtualMap F E g L (ExactGrothendieckGroup.ofRepresentation _ A) =
          ExactGrothendieckGroup.ofRepresentation _ ⟨A'.val, A'.property⟩ :=
        virtualMap_ofRepresentation F E g L A ⟨A'.val, A'.property⟩ (universeModelEquiv R.val)
      rw [hA, induce_ofRepresentation]
      refine (congrArg (virtualMap F E g M)
        (induce_ofRepresentation F M L h ⟨A.val, A.property⟩)).trans ?_
      exact virtualMap_ofRepresentation F E g M _ _
        (restrictInducedEquiv F E g h A A' (universeModelEquiv R.val))
  have hx := LinearMap.congr_fun hc x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
  exact hx

end Langlands.LocalFactor.NonabelianSystem.FieldTransport
