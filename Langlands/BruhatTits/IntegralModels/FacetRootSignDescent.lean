import Langlands.BruhatTits.IntegralModels.FacetRootSignBaseChange
import Langlands.BruhatTits.IntegralModels.Transport.Model
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.DynamicCentralizer
import Langlands.GroupScheme.IntegralModel.GenericRigidity

/-! # Descent of the facet root identity through coefficient change and subtori

The facet sign formula, in its root form, descends from a split integral torus
of the base-changed and transported source model to a split integral torus of
the original source model mapping into it. Over a strictly Henselian discrete
valuation ring, a generic factorization of one split integral torus through a
closed split integral torus extends to an integral homomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

/-- The base-changed quotient is of finite type when the quotient is. -/
instance SpecialFibreQuotientData.baseChange_quotient_locallyOfFiniteType
    {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
    [LocallyOfFiniteType Q.quotient.X.hom] :
    LocallyOfFiniteType (Q.baseChange A L).quotient.X.hom := by
  change LocallyOfFiniteType (pullback.snd Q.quotient.X.hom _)
  infer_instance

namespace RelativeComponentModelHom

variable {D D' : RelativeComponentModelData R K G} (φ : RelativeComponentModelHom D' D)
  (Q : SpecialFibreQuotientData D)
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D' S i)

/-- **Descent of the root-form sign formula through coefficient change,
transport and restriction.** Let `T'` be a split integral torus of the
base change of `D'` to `A`, transported along an isomorphism `e` of generic
groups, and let `ρ` map the base change of the split integral torus `T` into
`T'`, compatibly with the inclusions. Let the sign functions satisfy
`σ m = σ' ψ` whenever the base change of `m` is `ρ ≫ ψ`. If the roots of the
special fibre of `T'` in the reductive image are the quotient roots with
`σ' ≥ 0`, then the roots of the special fibre of `T` in the original
reductive image are the quotient roots with `σ ≥ 0`. -/
theorem roots_reductiveImageTorusMap_of_baseChange_transport
    [LocallyOfFiniteType Q.quotient.X.hom] (hT : IsSplitTorus T.torus.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (e : (GroupScheme.baseChange (Spec.algebraMap K L)).obj G ≅ H)
    {S' : CommGroupScheme (Spec (CommRingCat.of L))} {i' : S'.toGrp ⟶ H}
    (T' : IntegralTorusData ((D'.baseChange A L).transport e) S' i')
    (hT' : IsSplitTorus T'.torus.toGrp)
    (ρ : (CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T.torus ⟶ T'.torus)
    (hρ : CommGroupScheme.groupHom ρ ≫ T'.inclusion = T.baseChangeInclusion A L)
    (σ : characterLattice T.torus → ℝ) (σ' : characterLattice T'.torus → ℝ)
    (hσ : ∀ m ψ, characterLattice.baseChange (Spec.algebraMap R A) T.torus m = ρ ≫ ψ →
      σ m = σ' ψ)
    (h : roots (((φ.baseChange A L).transport e).reductiveImageTorusMap
          ((Q.baseChange A L).transport e) T') =
      {χ | χ ∈ roots (((φ.baseChange A L).transport e).quotientTorusInclusion
          ((Q.baseChange A L).transport e) T') ∧
        0 ≤ σ' ((T'.specialCharacterEquiv hT').symm χ)}) :
    roots (φ.reductiveImageTorusMap Q T) =
      {χ | χ ∈ roots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ σ ((T.specialCharacterEquiv hT).symm χ)} := by
  let T'' : IntegralTorusData (D'.baseChange A L) _ _ :=
    IntegralTorusData.ofInclusion (D'.baseChange A L) T'.torus T'.inclusion
  have hT'' : IsSplitTorus T''.torus.toGrp := hT'
  let bcE := characterLattice.baseChangeEquiv (Spec.algebraMap R A) T.torus hT
  have key := φ.roots_reductiveImageTorusMap_of_baseChange A L Q T hT
    (fun m' => σ (bcE.symm m'))
    ((φ.baseChange A L).roots_reductiveImageTorusMap_of_comp (Q.baseChange A L)
      (T.baseChange A L) T'' (T.isSplitTorus_baseChange A L hT) hT'' ρ hρ
      (fun m' => σ (bcE.symm m')) σ'
      (fun ψ => hσ _ ψ (bcE.apply_symm_apply (ρ ≫ ψ))) h)
  rw [key]
  ext χ
  exact and_congr Iff.rfl (by
    rw [show characterLattice.baseChange (Spec.algebraMap R A) T.torus
        ((T.specialCharacterEquiv hT).symm χ) = bcE ((T.specialCharacterEquiv hT).symm χ)
        from rfl, AddEquiv.symm_apply_apply])

end RelativeComponentModelHom

end Coefficients

section TorusExtension

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A split torus over `R`, as an integral model of its own generic fibre. -/
def IntegralModel.ofSplitTorus (T : CommGroupScheme (Spec (CommRingCat.of R)))
    (hT : IsSplitTorus T.toGrp) :
    IntegralModel R K ((GroupScheme.baseChange (Spec.algebraMap R K)).obj T.toGrp) :=
  haveI := hT.isAffineHom
  haveI := hT.smooth
  { group := T.toGrp
    genericIso := Iso.refl _ }

@[simp] theorem IntegralModel.ofSplitTorus_group (T : CommGroupScheme (Spec (CommRingCat.of R)))
    (hT : IsSplitTorus T.toGrp) :
    (IntegralModel.ofSplitTorus (K := K) T hT).group = T.toGrp := rfl

variable [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- **Extension of a generic factorization of split tori.** Over a Henselian
discrete valuation ring with separably closed residue field, let `j : T → N`
and a closed `k : A → N` be homomorphisms from split tori to an integral model.
If the generic fibre of `j` factors through the generic fibre of `k`, then `j`
factors through `k` by a homomorphism of tori with the given generic fibre. -/
theorem exists_torusHom_of_generic_factor (N : IntegralModel R K G)
    (T A : CommGroupScheme (Spec (CommRingCat.of R)))
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    (j : T.toGrp ⟶ N.group) (k : A.toGrp ⟶ N.group) (hk : IsClosedSubgroup k)
    (g : (GroupScheme.baseChange (Spec.algebraMap R K)).obj T.toGrp ⟶
      (GroupScheme.baseChange (Spec.algebraMap R K)).obj A.toGrp)
    (hg : g ≫ (GroupScheme.baseChange (Spec.algebraMap R K)).map k =
      (GroupScheme.baseChange (Spec.algebraMap R K)).map j) :
    ∃ ρ : T ⟶ A, CommGroupScheme.groupHom ρ ≫ k = j ∧
      (GroupScheme.baseChange (Spec.algebraMap R K)).map (CommGroupScheme.groupHom ρ) = g := by
  let MT := IntegralModel.ofSplitTorus (K := K) T hT
  let MA := IntegralModel.ofSplitTorus (K := K) A hA
  let φA : MA.Hom N ((GroupScheme.baseChange (Spec.algebraMap R K)).map k ≫ N.genericIso.hom) :=
    { hom := k
      generic_comm := (Category.id_comp _).symm }
  let φT : MT.Hom N ((GroupScheme.baseChange (Spec.algebraMap R K)).map j ≫ N.genericIso.hom) :=
    { hom := j
      generic_comm := (Category.id_comp _).symm }
  have hpts : ∀ x ∈ MT.integralPoints, rationalPoints.map g x ∈ MA.integralPoints := by
    intro x hx
    apply φA.mem_integralPoints_of_map_mem hk
    rw [← rationalPoints_map_comp_apply_of_ring, ← Category.assoc, hg]
    exact φT.integralPoints_map_le x hx
  have hsmooth : MT.IsSmooth := hT.smooth
  obtain ⟨ψ⟩ := IntegralModel.smoothHomExtension R K _ _ g MT MA hsmooth hpts
  have hψ : (GroupScheme.baseChange (Spec.algebraMap R K)).map ψ.hom = g := by
    have h := ψ.generic_comm
    simpa only [MT, MA, IntegralModel.ofSplitTorus, Iso.refl_hom, Category.comp_id,
      Category.id_comp] using h
  refine ⟨Additive.ofMul ψ.hom, ?_, hψ⟩
  apply IntegralModel.hom_eq_of_generic (M := MT) (N := N)
  change (GroupScheme.baseChange (Spec.algebraMap R K)).map (ψ.hom ≫ k) = _
  rw [Functor.map_comp, hψ, hg]

end TorusExtension

end Langlands.BruhatTits.IntegralModels
