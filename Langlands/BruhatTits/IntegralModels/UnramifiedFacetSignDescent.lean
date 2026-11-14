import Langlands.BruhatTits.IntegralModels.FacetRootSignDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetLieWeightSignStatement
import Langlands.Geometry.Building.UnramifiedDescendedApartmentTorusStatement
import Langlands.Geometry.Building.DescendedApartmentLinearPart
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerRoots
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelReduction
import Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalProof
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.IntegralModel.TwistCoefficientComparison
import Langlands.GroupScheme.Reductive.PinningScalarCoherence
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Langlands.Galois.Local.SeparableHenselian

/-! # Descent of the facet Lie-weight sign formula from the maximal unramified extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

section SplitTorus

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

/-- A split integral torus of the neutral model of a model pair, regarded as
integral torus data of the pair: the same torus and inclusion, with the generic
identification on underlying group schemes. -/
def IntegralSplitTorusData.toIntegralTorusData {D : RelativeComponentModelData R K G}
    (A : IntegralSplitTorusData D.neutral i) : IntegralTorusData D S i where
  torus := A.torus
  genericIso := underlyingTorusIso A.genericIso
  inclusion := A.inclusion
  generic_comm := A.generic_comm

namespace IntegralSplitTorusData

variable {D : RelativeComponentModelData R K G} (A : IntegralSplitTorusData D.neutral i)

@[simp] theorem toIntegralTorusData_torus : A.toIntegralTorusData.torus = A.torus := rfl

@[simp] theorem toIntegralTorusData_inclusion :
    A.toIntegralTorusData.inclusion = A.inclusion := rfl

theorem toIntegralTorusData_genericIso_hom :
    A.toIntegralTorusData.genericIso.hom = CommGroupScheme.groupHom A.genericIso.hom := rfl

theorem toIntegralTorusData_genericIso_inv :
    A.toIntegralTorusData.genericIso.inv = CommGroupScheme.groupHom A.genericIso.inv := rfl

end IntegralSplitTorusData

end SplitTorus

section ReductiveQuotient

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

private instance neutralSpecialFibre_smooth (D : RelativeComponentModelData R K G) :
    Smooth D.neutral.specialFibre.X.hom := by
  have : Smooth D.neutral.group.X.hom := D.neutral_smooth
  change Smooth (pullback.snd D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

private instance neutralSpecialFibre_isAffineHom (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (pullback.snd D.neutral.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

/-- **Base change of a maximal reductive quotient along a separable algebraic
residue field extension.** If the residue field extension of `R → A` is
separable and algebraic, the residue-field base change of a maximal reductive
quotient of the neutral special fibre is a maximal reductive quotient of the
special fibre of the base-changed model. -/
theorem SpecialFibreQuotientData.isReductiveQuotient_baseChange
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
    (hQ : Q.IsReductiveQuotient) : (Q.baseChange A L).IsReductiveQuotient := by
  have hconn : ConnectedSpace D.neutral.specialFibre.X.left :=
    D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (separableAlgebraicUnipotentRadical (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A) D.neutral.specialFibre inferInstance inferInstance
      hconn).1 Q.radical Q.radicalInclusion hQ.1
    exact h1.comp_iso _
  · have h2 := (hQ.2.1.baseChange (algebraBaseMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField A))).comapIso (specialFibreSquareIso A D.neutral.group)
    change RelativeRoot.IsFppfQuotient (SubgroupFunctor.range
      ((GroupScheme.baseChange _).map Q.radicalInclusion ≫
        (specialFibreSquareIso A D.neutral.group).hom)) _
    rw [SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
    exact h2
  · exact hQ.2.2.baseChange_of_algebraicExtension

end ReductiveQuotient


section GenericFactor

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

omit [IsDomain R] [IsFractionRing R K] [IsDomain A] [IsFractionRing A L] in
/-- The two coefficient towers give the same scheme map. -/
theorem coefficientSquare_spec :
    Spec.algebraMap A L ≫ Spec.algebraMap R A =
      Spec.algebraMap K L ≫ Spec.algebraMap R K := by
  calc
    _ = Spec.algebraMap R L := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply R A L x).symm
    _ = _ := by
      symm
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply R K L x).symm

variable {D' : RelativeComponentModelData R K G}
  {S₀ : CommGroupScheme (Spec (CommRingCat.of K))} {i₀ : S₀.toGrp ⟶ G}
  (𝒯 : IntegralTorusData D' S₀ i₀)
  {H : GroupScheme (Spec (CommRingCat.of L))}
  (ε : (GroupScheme.baseChange (Spec.algebraMap K L)).obj G ≅ H)
  {S' : CommGroupScheme (Spec (CommRingCat.of L))} {i' : S'.toGrp ⟶ H}
  (T' : IntegralTorusData ((D'.baseChange A L).transport ε) S' i')
  (f : (GroupScheme.baseChange (Spec.algebraMap K L)).obj S₀.toGrp ⟶ S'.toGrp)

/-- The generic map from the base change of the torus of `𝒯` to the generic
fibre of `T'` determined by a generic factorization `f`: the coefficient-square
comparison, the generic identification of `𝒯`, `f`, and the inverse generic
identification of `T'`. -/
def comparisonGenericMap :
    (GroupScheme.baseChange (Spec.algebraMap A L)).obj
        ((GroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus.toGrp) ⟶
      (GroupScheme.baseChange (Spec.algebraMap A L)).obj T'.torus.toGrp :=
  (Descent.squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
      (Spec.algebraMap R K) (Spec.algebraMap K L) (coefficientSquare_spec A L)
      𝒯.torus.toGrp).hom ≫
    (GroupScheme.baseChange (Spec.algebraMap K L)).map 𝒯.genericIso.hom ≫ f ≫
      T'.genericIso.inv

/-- If `f` factors the transported base change of the generic inclusion of `𝒯`
through the generic inclusion of `T'`, then the comparison generic map factors the
base-changed inclusion of `𝒯` through the inclusion of `T'`. -/
theorem comparisonGenericMap_comp_inclusion
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i₀ ≫ ε.hom) :
    comparisonGenericMap A L 𝒯 ε T' f ≫
        (GroupScheme.baseChange (Spec.algebraMap A L)).map T'.inclusion =
      (GroupScheme.baseChange (Spec.algebraMap A L)).map (𝒯.baseChangeInclusion A L) := by
  apply (cancel_mono ((D'.neutral.baseChangeGenericIso A L).hom ≫ ε.hom)).mp
  have h1 : (GroupScheme.baseChange (Spec.algebraMap A L)).map T'.inclusion ≫
      (D'.neutral.baseChangeGenericIso A L).hom ≫ ε.hom = T'.genericIso.hom ≫ i' :=
    T'.generic_comm
  rw [Category.assoc, h1]
  simp only [comparisonGenericMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hf, IntegralModel.baseChangeGenericIso_eq_square]
  simp only [IntegralModel.baseChangeSquareIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  have hn : (GroupScheme.baseChange (Spec.algebraMap A L)).map (𝒯.baseChangeInclusion A L) ≫
      (Descent.squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap R K) (Spec.algebraMap K L) (coefficientSquare_spec A L)
        D'.neutral.group).hom =
      (Descent.squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap R K) (Spec.algebraMap K L) (coefficientSquare_spec A L)
        𝒯.torus.toGrp).hom ≫
        (GroupScheme.baseChange (Spec.algebraMap K L)).map
          ((GroupScheme.baseChange (Spec.algebraMap R K)).map 𝒯.inclusion) :=
    Descent.squareComparison_naturality _ _ _ _ _ 𝒯.inclusion
  have h2 : (GroupScheme.baseChange (Spec.algebraMap K L)).map
        ((GroupScheme.baseChange (Spec.algebraMap R K)).map 𝒯.inclusion) ≫
        (GroupScheme.baseChange (Spec.algebraMap K L)).map D'.neutral.genericIso.hom ≫ ε.hom =
      (GroupScheme.baseChange (Spec.algebraMap K L)).map 𝒯.genericIso.hom ≫
        (GroupScheme.baseChange (Spec.algebraMap K L)).map i₀ ≫ ε.hom := by
    rw [← Functor.map_comp_assoc, 𝒯.generic_comm, Functor.map_comp_assoc]
  rw [← Category.assoc ((GroupScheme.baseChange (Spec.algebraMap A L)).map
    (𝒯.baseChangeInclusion A L)), hn]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) h2.symm

/-- **Characters through the comparison generic map.** Let `ρ` map the base change of
the torus of `𝒯` to the torus of `T'`, with generic fibre the comparison generic map
of `f`. If the base change of an integral character `m` of `𝒯` is `ρ ≫ ψ`, then
the base change of the generic character of `m` is the generic character of `ψ`
composed with `f`. -/
theorem baseChange_genericCharacter_eq_of_comparisonGenericMap
    (ρ : (CommGroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus ⟶ T'.torus)
    (hρ : (GroupScheme.baseChange (Spec.algebraMap A L)).map (CommGroupScheme.groupHom ρ) =
      comparisonGenericMap A L 𝒯 ε T' f)
    (m : characterLattice 𝒯.torus) (ψ : characterLattice T'.torus)
    (hm : characterLattice.baseChange (Spec.algebraMap R A) 𝒯.torus m = ρ ≫ ψ) :
    characterLattice.baseChange (Spec.algebraMap K L) S₀ (𝒯.genericCharacter m) =
      Additive.ofMul f ≫ T'.genericCharacter ψ := by
  have t1 := Descent.characterBaseChange_tower (Spec.algebraMap R A) (Spec.algebraMap A L)
    (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L) 𝒯.torus m
  have t2 := Descent.characterBaseChange_tower (Spec.algebraMap R K) (Spec.algebraMap K L)
    (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus m
  rw [hm, characterLattice.baseChange_precomp] at t1
  have hr : characterLattice.baseChange (Spec.algebraMap K L ≫ Spec.algebraMap R K)
        𝒯.torus m =
      (Descent.commPullbackComparison _ _ _ (coefficientSquare_spec A L) 𝒯.torus).inv ≫
        (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
    rw [t1, Iso.inv_hom_id_assoc]
  have hgen : 𝒯.genericCharacter m =
      (show S₀ ⟶ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒯.torus from
        Additive.ofMul 𝒯.genericIso.inv) ≫
        characterLattice.baseChange (Spec.algebraMap R K) 𝒯.torus m := rfl
  have hgen' : T'.genericCharacter ψ =
      (show S' ⟶ (CommGroupScheme.baseChange (Spec.algebraMap A L)).obj T'.torus from
        Additive.ofMul T'.genericIso.inv) ≫
        characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := rfl
  have key : (GroupScheme.baseChange (Spec.algebraMap K L)).map 𝒯.genericIso.inv ≫
      (Descent.pullbackComparison (Spec.algebraMap R K) (Spec.algebraMap K L)
        (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus.toGrp).hom ≫
      (Descent.pullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L)
        𝒯.torus.toGrp).inv ≫
      comparisonGenericMap A L 𝒯 ε T' f = f ≫ T'.genericIso.inv := by
    simp only [comparisonGenericMap, Descent.squareComparison, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hρ' : (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ =
      Additive.ofMul (comparisonGenericMap A L 𝒯 ε T' f) :=
    congrArg Additive.ofMul hρ
  calc characterLattice.baseChange (Spec.algebraMap K L) S₀ (𝒯.genericCharacter m)
      = (CommGroupScheme.baseChange (Spec.algebraMap K L)).map
          (show S₀ ⟶ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒯.torus from
            Additive.ofMul 𝒯.genericIso.inv) ≫
          (Descent.commPullbackComparison (Spec.algebraMap R K) (Spec.algebraMap K L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus).hom ≫
          (Descent.commPullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L)
            𝒯.torus).inv ≫
          (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
        rw [hgen, characterLattice.baseChange_precomp, t2, hr]
    _ = ((CommGroupScheme.baseChange (Spec.algebraMap K L)).map
          (show S₀ ⟶ (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj 𝒯.torus from
            Additive.ofMul 𝒯.genericIso.inv) ≫
          (Descent.commPullbackComparison (Spec.algebraMap R K) (Spec.algebraMap K L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) rfl 𝒯.torus).hom ≫
          (Descent.commPullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
            (Spec.algebraMap K L ≫ Spec.algebraMap R K) (coefficientSquare_spec A L)
            𝒯.torus).inv ≫
          (CommGroupScheme.baseChange (Spec.algebraMap A L)).map ρ) ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
        simp only [Category.assoc]
    _ = (show (CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S₀ ⟶
            (CommGroupScheme.baseChange (Spec.algebraMap A L)).obj T'.torus from
          Additive.ofMul (f ≫ T'.genericIso.inv)) ≫
          characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ := by
        congr 1
        rw [hρ']
        exact congrArg Additive.ofMul key
    _ = Additive.ofMul f ≫ T'.genericCharacter ψ :=
        Category.assoc
          (show (CommGroupScheme.baseChange (Spec.algebraMap K L)).obj S₀ ⟶ S' from
            Additive.ofMul f)
          (show S' ⟶ (CommGroupScheme.baseChange (Spec.algebraMap A L)).obj T'.torus from
            Additive.ofMul T'.genericIso.inv)
          (characterLattice.baseChange (Spec.algebraMap A L) T'.torus ψ)

end GenericFactor

section RootForm

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {source target : RelativeComponentModelData R K G}
  (φ : RelativeComponentModelHom source target) (Q : SpecialFibreQuotientData target)
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData source S i)

attribute [local instance] neutralSpecialFibre_affine neutralSpecialFibre_isAffine
  quotient_isAffine

/-- A Lie-weight sign identity with an arbitrary sign function on generic characters,
in root form: the roots of the special-fibre torus in the reductive image are the
quotient roots whose generic character has nonnegative sign. -/
theorem RelativeComponentModelHom.roots_eq_of_nonzeroLieImageWeights_eq
    (hT : IsSplitTorus T.torus.toGrp) (σ : characterLattice S → ℝ)
    (h : nonzeroLieImageWeights (φ.quotientTorusInclusion Q T) (φ.reductiveImageInclusion Q) =
      {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ σ ((T.characterSpecialization hT).symm χ)}) :
    roots (φ.reductiveImageTorusMap Q T) =
      {χ | χ ∈ roots (φ.quotientTorusInclusion Q T) ∧
        0 ≤ σ (T.genericCharacter ((T.specialCharacterEquiv hT).symm χ))} := by
  rw [φ.nonzeroLieImageWeights_quotientTorusInclusion] at h
  exact h

end RootForm

section GenericDescent

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsDiscreteValuationRing A] [HenselianLocalRing A]
  [IsSepClosed (IsLocalRing.ResidueField A)]

/-- **The comparison map of tori.** Over a Henselian discrete valuation ring `A` with
separably closed residue field, let `A'` be a closed split integral torus of the
transported base change of `D'`, and let `f` factor the transported base change of the
generic inclusion of the split integral torus `𝒯` through the generic inclusion of `A'`.
Then the base change of `𝒯` maps into `A'`, compatibly with the inclusions, with
generic fibre the comparison generic map of `f`. -/
theorem exists_torusHom_of_transport {D' : RelativeComponentModelData R K G}
    {S₀ : CommGroupScheme (Spec (CommRingCat.of K))} {i₀ : S₀.toGrp ⟶ G}
    (𝒯 : IntegralTorusData D' S₀ i₀) (hT : IsSplitTorus 𝒯.torus.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (ε : (GroupScheme.baseChange (Spec.algebraMap K L)).obj G ≅ H)
    {S' : CommGroupScheme (Spec (CommRingCat.of L))} {i' : S'.toGrp ⟶ H}
    (A' : IntegralSplitTorusData ((D'.baseChange A L).transport ε).neutral i')
    (hA' : IsClosedSubgroup A'.inclusion)
    (f : (GroupScheme.baseChange (Spec.algebraMap K L)).obj S₀.toGrp ⟶ S'.toGrp)
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i₀ ≫ ε.hom) :
    ∃ (ρ : (CommGroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus ⟶ A'.torus),
      CommGroupScheme.groupHom ρ ≫ A'.inclusion = 𝒯.baseChangeInclusion A L ∧
        (GroupScheme.baseChange (Spec.algebraMap A L)).map (CommGroupScheme.groupHom ρ) =
          comparisonGenericMap A L 𝒯 ε A'.toIntegralTorusData f :=
  exists_torusHom_of_generic_factor ((D'.baseChange A L).transport ε).neutral
    ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj 𝒯.torus) A'.torus
    (𝒯.isSplitTorus_baseChange A L hT) A'.isSplit (𝒯.baseChangeInclusion A L) A'.inclusion hA'
    _ (comparisonGenericMap_comp_inclusion A L 𝒯 ε A'.toIntegralTorusData f hf)

/-- **Descent of the root-form sign formula along a closed comparison torus.** In the
setting of `exists_torusHom_of_transport`, let the sign functions satisfy `σ χ = σ' ψ`
whenever the base change of the generic character `χ` of `𝒯` is `ψ ∘ f`. If the roots
of the special fibre of `A'` in the transported reductive image are the transported
quotient roots with `σ' ≥ 0`, then the roots of the special fibre of `𝒯` in the original
reductive image are the quotient roots with `σ ≥ 0`. -/
theorem RelativeComponentModelHom.roots_of_transport_comparisonGenericMap
    [IsLocalRing R] [IsLocalHom (algebraMap R A)]
    {D D' : RelativeComponentModelData R K G} (φ : RelativeComponentModelHom D' D)
    (Q : SpecialFibreQuotientData D) [LocallyOfFiniteType Q.quotient.X.hom]
    {S₀ : CommGroupScheme (Spec (CommRingCat.of K))} {i₀ : S₀.toGrp ⟶ G}
    (𝒯 : IntegralTorusData D' S₀ i₀) (hT : IsSplitTorus 𝒯.torus.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (ε : (GroupScheme.baseChange (Spec.algebraMap K L)).obj G ≅ H)
    {S' : CommGroupScheme (Spec (CommRingCat.of L))} {i' : S'.toGrp ⟶ H}
    (A' : IntegralSplitTorusData ((D'.baseChange A L).transport ε).neutral i')
    (hA' : IsClosedSubgroup A'.inclusion)
    (f : (GroupScheme.baseChange (Spec.algebraMap K L)).obj S₀.toGrp ⟶ S'.toGrp)
    (hf : f ≫ i' = (GroupScheme.baseChange (Spec.algebraMap K L)).map i₀ ≫ ε.hom)
    (σ : characterLattice S₀ → ℝ) (σ' : characterLattice S' → ℝ)
    (hσ : ∀ χ ψ, characterLattice.baseChange (Spec.algebraMap K L) S₀ χ =
      Additive.ofMul f ≫ ψ → σ χ = σ' ψ)
    (h : roots (((φ.baseChange A L).transport ε).reductiveImageTorusMap
          ((Q.baseChange A L).transport ε) A'.toIntegralTorusData) =
      {χ | χ ∈ roots (((φ.baseChange A L).transport ε).quotientTorusInclusion
          ((Q.baseChange A L).transport ε) A'.toIntegralTorusData) ∧
        0 ≤ σ' (A'.toIntegralTorusData.genericCharacter
          ((A'.toIntegralTorusData.specialCharacterEquiv A'.isSplit).symm χ))}) :
    roots (φ.reductiveImageTorusMap Q 𝒯) =
      {χ | χ ∈ roots (φ.quotientTorusInclusion Q 𝒯) ∧
        0 ≤ σ (𝒯.genericCharacter ((𝒯.specialCharacterEquiv hT).symm χ))} := by
  obtain ⟨ρ, hρ, hρg⟩ := exists_torusHom_of_transport A L 𝒯 hT ε A' hA' f hf
  exact φ.roots_reductiveImageTorusMap_of_baseChange_transport A L Q 𝒯 hT ε
    A'.toIntegralTorusData A'.isSplit ρ hρ (fun m => σ (𝒯.genericCharacter m))
    (fun ψ => σ' (A'.toIntegralTorusData.genericCharacter ψ))
    (fun m ψ hm => hσ _ _ (baseChange_genericCharacter_eq_of_comparisonGenericMap A L 𝒯 ε
      A'.toIntegralTorusData f ρ hρg m ψ hm)) h

end GenericDescent

section Unramified

open Langlands.LocalGalois.Separable Langlands.Geometry.Building
open Langlands.GroupScheme.GaloisPointComparison
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance unramifiedFacetSignIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedFacetSignIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedFacetSignIntegerLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- The residue-field algebra induced by the integral extension `𝒪[F] → O` is the
published residue map. -/
theorem unramifiedResidueAlgebra_eq :
    (inferInstance : Algebra (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F))) = (residueToFixedField F).toAlgebra := by
  apply Algebra.algebra_ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  rfl

/-- The residue field of `O` is algebraic over the residue field of `𝒪[F]`. -/
theorem unramifiedResidue_isAlgebraic :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  have h := (fixedFieldResidueIsAlgClosure F).isAlgebraic
  convert h
  exact unramifiedResidueAlgebra_eq

/-- The residue field of `O` is separable over the finite residue field of `𝒪[F]`. -/
theorem unramifiedResidue_isSeparable :
    Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[F])
      (IsLocalRing.ResidueField (fixedFieldIntegers F)) := by
  have : Finite (IsLocalRing.ResidueField ↥𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  have := unramifiedResidue_isAlgebraic (F := F)
  infer_instance

set_option maxHeartbeats 1600000 in
/-- Transporting a model over `O` by the inner automorphism `Int(g⁻¹)` turns the
integral points `E(0) ∩ G(K)_{g Y}` into `E(0) ∩ G(K)_Y`, by normality of `E(0)`. -/
theorem integralPoints_transport_innerIso_inv
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (Y : Set C.Apartment)
    (M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hM : M.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y)) :
    (M.transport ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹)).integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Y) := by
  have hzero : E.zeroPoints.map
      (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom) =
        E.zeroPoints := by
    rw [rationalPoints_map_innerIso]
    have hN := E.normal_zeroPoints
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy g⁻¹
    · intro x hx
      refine ⟨g * x * g⁻¹, hN.conj_mem x hx g, ?_⟩
      change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
      simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have hset : (fun x => g • C.apartmentMap x) '' Y =
      (fun y => g • y) '' (C.apartmentMap '' Y) :=
    (Set.image_image _ _ _).symm
  have hfix : (C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y)).map
      (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom) =
        C.pointwiseFixer (C.apartmentMap '' Y) := by
    rw [hset, rationalPoints_map_innerIso]
    exact pointwiseFixer_smul_image_map_conj C g _
  have h1 := IntegralModel.transport_integralPoints M
    ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹)
  have h2 := congrArg (Subgroup.map
    (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom)) hM
  have h3 := Subgroup.map_inf_eq E.zeroPoints
    (C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Y))
    (rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g⁻¹).hom)
    (rationalPoints_map_injective_of_iso _)
  exact h1.trans (h2.trans (h3.trans (by rw [hzero, hfix])))

/-- The base change of an affine group scheme to the maximal unramified extension is affine,
by pullback-stability of affine morphisms. -/
private instance unramifiedFacetSignAffineHom
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The base change of the inner automorphism by `g` is undone by the inner
automorphism of the base change by the inverse of the extended point. -/
theorem baseChange_innerIso_hom_comp_innerIso_inv
    {G : GroupScheme (Spec (CommRingCat.of F))} (g : rationalPoints G) :
    (GroupScheme.baseChange (Spec.algebraMap F (inertiaFixedField F))).map (G.innerIso g).hom ≫
        ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)⁻¹).hom = 𝟙 _ := by
  rw [baseChange_innerIso_hom, innerIso_inv_hom, rationalExtend_eq_baseChangeBasePoint]
  exact Iso.hom_inv_id _

/-- The integral points of a model over `𝒪[F]` characterized, after base change to `O`,
by a facet `g • Fa` of the descended building become, after transport by `Int(g⁻¹)`,
the zero fixer of the image `a(Fa)` in the apartment of `C`. -/
theorem integralPoints_transport_baseChangeUnramified
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (ha : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints G) (Fa : Set B.Apartment) (M : IntegralModel ↥𝒪[F] F G)
    (hM : M.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' (B.translatedApartmentMap g '' Fa))) :
    (M.baseChangeUnramified.transport ((baseChanged F (inertiaFixedField F) G).innerIso
        (rationalExtend F (inertiaFixedField F) G g)⁻¹)).integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' (a '' Fa)) := by
  have hset : e '' (B.translatedApartmentMap g '' Fa) =
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) '' (a '' Fa) := by
    rw [Set.image_image, Set.image_image]
    apply Set.image_congr
    intro w _
    change e (g • B.apartmentMap w) = _
    rw [he, ha]
  exact integralPoints_transport_innerIso_inv C E _ (a '' Fa) _ (hset ▸ hM)

/-- The factorization `f` of the base change of `B.i` also factors the transported base
change of the conjugated inclusion `B.i ≫ Int(g)`. -/
theorem comp_eq_baseChange_comp_innerIso_inv
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)
    (hf : f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (g : rationalPoints G) :
    f ≫ C.i = (GroupScheme.baseChange (Spec.algebraMap F (inertiaFixedField F))).map
      (B.i ≫ (G.innerIso g).hom) ≫ ((baseChanged F (inertiaFixedField F) G).innerIso
        (rationalExtend F (inertiaFixedField F) G g)⁻¹).hom := by
  rw [Functor.map_comp, Category.assoc, baseChange_innerIso_hom_comp_innerIso_inv,
    Category.comp_id]
  exact hf

set_option maxHeartbeats 1600000 in
/-- The sign formula over `O`, for the transported base changes and the comparison torus
`A'`, in root form, at a point `a x` and the displacement `f_*(v)`. -/
theorem roots_transport_of_unramifiedSign
    (hI : UnramifiedFacetLieWeightSignStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (ha : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
    (hfacet : ∀ w : B.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
        AffineRootSystem.facet B.affineRoots w)
    (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)
    (hf : f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints G) (Fa Fa' : Set B.Apartment)
    (hface : AffineRootSystem.IsFaceOf B.affineRoots Fa Fa')
    (D D' : RelativeComponentModelData ↥𝒪[F] F G)
    (hpts : ((D.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
        ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)⁻¹)).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' (a '' Fa)))
    (hpts' : ((D'.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
        ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)⁻¹)).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' (a '' Fa')))
    (φ : RelativeComponentModelHom D' D) (Q : SpecialFibreQuotientData D)
    (hQ : Q.IsReductiveQuotient)
    (A' : IntegralSplitTorusData ((D'.baseChange (fixedFieldIntegers F)
        (inertiaFixedField F)).transport ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)⁻¹)).neutral C.i)
    {x : B.Apartment} (hx : x ∈ Fa) (v : RealTorusSpace.V B.S)
    (hv : (Submodule.Quotient.mk v : TranslationSpace B.i) +ᵥ x ∈ Fa') :
    roots (((φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
        ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)⁻¹)).reductiveImageTorusMap
        ((Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
          ((baseChanged F (inertiaFixedField F) G).innerIso
            (rationalExtend F (inertiaFixedField F) G g)⁻¹)) A'.toIntegralTorusData) =
      {χ | χ ∈ roots (((φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
          ((baseChanged F (inertiaFixedField F) G).innerIso
            (rationalExtend F (inertiaFixedField F) G g)⁻¹)).quotientTorusInclusion
          ((Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
            ((baseChanged F (inertiaFixedField F) G).innerIso
              (rationalExtend F (inertiaFixedField F) G g)⁻¹)) A'.toIntegralTorusData) ∧
        0 ≤ RealTorusSpace.eval C.S (A'.toIntegralTorusData.genericCharacter
          ((A'.toIntegralTorusData.specialCharacterEquiv A'.isSplit).symm χ))
          (descendedCocharacterMap B C f v)} := by
  have := unramifiedResidue_isAlgebraic (F := F)
  have := unramifiedResidue_isSeparable (F := F)
  obtain ⟨x₁, -, hfaceC, hsub, hsub'⟩ := AffineRootSystem.exists_isFaceOf_image hfacet hface hx
  have hvadd := descendedApartment_map_vadd e a he ha hf v x
  have hQ' := Q.isReductiveQuotient_baseChange (fixedFieldIntegers F) (inertiaFixedField F) hQ
  have hIx := hI F (baseChanged F (inertiaFixedField F) G) C E _ _ (a '' Fa) (a '' Fa')
    hfaceC hsub hsub'
    ((D.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
      ((baseChanged F (inertiaFixedField F) G).innerIso
        (rationalExtend F (inertiaFixedField F) G g)⁻¹))
    ((D'.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
      ((baseChanged F (inertiaFixedField F) G).innerIso
        (rationalExtend F (inertiaFixedField F) G g)⁻¹))
    ((IntegralModel.isSmooth_transport_iff _ _).2
      (D.neutral.isSmooth_baseChange _ _ D.neutral_smooth))
    ((IntegralModel.isSmooth_transport_iff _ _).2
      (D'.neutral.isSmooth_baseChange _ _ D'.neutral_smooth)) hpts hpts'
    ((φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport _)
    ((Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport _)
    A'.toIntegralTorusData A'.isSplit
    ((SpecialFibreQuotientData.isReductiveQuotient_transport_iff _ _).2 hQ')
    (a x) ⟨x, hx, rfl⟩ (descendedCocharacterMap B C f v)
    (by rw [← hvadd]; exact ⟨_, hv, rfl⟩)
  exact RelativeComponentModelHom.roots_eq_of_nonzeroLieImageWeights_eq _ _ _
    A'.isSplit (fun χ => RealTorusSpace.eval C.S χ (descendedCocharacterMap B C f v)) hIx


set_option maxHeartbeats 1600000 in
/-- The sign formula for the original models, from the sign formula over `O` applied to
the transported base changes and a closed split integral torus of the transported base
change of `D'` characterized by the zero fixer of `a(Fa')`. -/
theorem hasApartmentLieWeightSignFormula_of_transport
    (hI : UnramifiedFacetLieWeightSignStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (he : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (ha : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
    (hfacet : ∀ w : B.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
        AffineRootSystem.facet B.affineRoots w)
    (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)
    (hf : f ≫ C.i = (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints G) (Fa Fa' : Set B.Apartment)
    (hface : AffineRootSystem.IsFaceOf B.affineRoots Fa Fa')
    (D D' : RelativeComponentModelData ↥𝒪[F] F G)
    (hpts : ((D.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
        ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)⁻¹)).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' (a '' Fa)))
    (hpts' : ((D'.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).transport
        ((baseChanged F (inertiaFixedField F) G).innerIso
          (rationalExtend F (inertiaFixedField F) G g)⁻¹)).neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' (a '' Fa')))
    (φ : RelativeComponentModelHom D' D) (Q : SpecialFibreQuotientData D)
    (𝒯 : IntegralTorusData D' B.S (B.i ≫ (G.innerIso g).hom))
    (hQ : Q.IsReductiveQuotient) (hT : IsSplitTorus 𝒯.torus.toGrp) :
    φ.HasApartmentLieWeightSignFormula B Q 𝒯 hT Fa Fa' := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  have : LocallyOfFiniteType Q.quotient.X.hom := by
    have := hQ.2.2.smooth
    infer_instance
  obtain ⟨A', hA'⟩ := exists_unramifiedZeroFixerIntegralSplitTorusData C E _ (a '' Fa') hpts'
  rw [φ.hasApartmentLieWeightSignFormula_iff_roots]
  intro x hx v hv
  exact φ.roots_of_transport_comparisonGenericMap (fixedFieldIntegers F) (inertiaFixedField F) Q 𝒯
    hT _ A' hA' f (comp_eq_baseChange_comp_innerIso_inv B C f hf g)
    (fun χ => RealTorusSpace.eval B.S χ v)
    (fun ψ => RealTorusSpace.eval C.S ψ (descendedCocharacterMap B C f v))
    (fun χ ψ h => (eval_descendedCocharacterMap B C f ψ χ h v).symm)
    (roots_transport_of_unramifiedSign hI B C e a he ha hfacet f hf E g Fa Fa' hface D D'
      hpts hpts' φ Q hQ A' hx v hv)

set_option maxHeartbeats 1600000 in
/-- **Descent of the Lie-weight sign formula** (Kaletha–Prasad Axiom 4.1.22(3) for the
descended building, sign part). Assume the sign formula over the maximal unramified
extension (`UnramifiedFacetLieWeightSignStatement`) and that the base change of the
descended torus factors through the torus of the unramified apartment
(`UnramifiedDescendedApartmentTorusStatement`). Then, for all data of
`UnramifiedFacetCommonTorusStatement` with a split integral torus `𝒯`, the nonzero
weights of `S` on the Lie algebra of the image of `φ` in `Q` are the roots of `Q` that
are nonnegative on every vector carrying a point of `Fa` into `Fa'`. -/
theorem unramifiedFacetLieWeightSignFormula_of_descent
    (hI : UnramifiedFacetLieWeightSignStatement.{u})
    (hII : UnramifiedDescendedApartmentTorusStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting)
    (h₁ : P.SatisfiesBuildingAxiom R) (h₂ : P.HasBoundedOpenStabilizers)
    (h₃ : P.SatisfiesAffineApartmentAxiom T) (h₄ : P.HasRootReflections)
    (h₅ : P.SatisfiesApartmentAxioms) (h₆ : P.HasCompatibleApartmentFacets)
    (h₇ : P.HasTitsSystem)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (A : MaximalUnramified.SemilinearApartmentData C)
    (e : P.toValuationBuildingData.ReducedBuilding → C.ReducedBuilding)
    (a : P.toValuationBuildingData.Apartment →ᵃ[ℝ] C.Apartment)
    (he_inj : Function.Injective e)
    (he : ∀ (g : rationalPoints G) (z : P.toValuationBuildingData.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (ha : ∀ w : P.toValuationBuildingData.Apartment,
      e (P.toValuationBuildingData.apartmentMap w) = C.apartmentMap (a w))
    (hgal : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
        (z : P.toValuationBuildingData.ReducedBuilding),
      A.action σ (e z) = e z)
    (hfixed : ∀ y : C.ReducedBuilding,
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, A.action σ y = y) →
        ∃ z : P.toValuationBuildingData.ReducedBuilding, e z = y)
    (hspecial : ∀ z : P.toValuationBuildingData.ReducedBuilding,
      C.IsSpecialPoint (e z) → P.toValuationBuildingData.IsSpecialPoint z)
    (hfacet : ∀ w : P.toValuationBuildingData.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
        AffineRootSystem.facet P.toValuationBuildingData.affineRoots w)
    (hbounded : ∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) P.S.toGrp),
      ∀ w : P.toValuationBuildingData.Apartment,
        rationalPoints.map
            ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map P.i) s •
          e (P.toValuationBuildingData.apartmentMap w) =
            e (P.toValuationBuildingData.apartmentMap w))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fc' : BuildingFacet P.toValuationBuildingData)
    (g : rationalPoints G) (Fa Fa' : Set P.toValuationBuildingData.Apartment)
    (hface : AffineRootSystem.IsFaceOf P.toValuationBuildingData.affineRoots Fa Fa')
    (hFc : Fc.val = P.toValuationBuildingData.translatedApartmentMap g '' Fa)
    (hFc' : Fc'.val = P.toValuationBuildingData.translatedApartmentMap g '' Fa')
    (D D' : RelativeComponentModelData ↥𝒪[F] F G)
    (hD : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hD' : D'.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val))
    (φ : RelativeComponentModelHom D' D) (Q : SpecialFibreQuotientData D)
    (𝒯 : IntegralTorusData D' P.toValuationBuildingData.S
      (P.toValuationBuildingData.i ≫ (G.innerIso g).hom))
    (hQ : Q.IsReductiveQuotient) (hT : IsSplitTorus 𝒯.torus.toGrp) :
    φ.HasApartmentLieWeightSignFormula P.toValuationBuildingData Q 𝒯 hT Fa Fa' := by
  obtain ⟨f, hf⟩ := hII F G P R T h₁ h₂ h₃ h₄ h₅ h₆ h₇ C A e a he_inj he ha hgal hfixed
    hspecial hfacet hbounded
  exact hasApartmentLieWeightSignFormula_of_transport hI P.toValuationBuildingData C e a he ha
    hfacet f hf E g Fa Fa' hface D D'
    (integralPoints_transport_baseChangeUnramified P.toValuationBuildingData C e a he ha E g
      Fa D.neutral (by rw [← hFc]; exact hD))
    (integralPoints_transport_baseChangeUnramified P.toValuationBuildingData C e a he ha E g
      Fa' D'.neutral (by rw [← hFc']; exact hD'))
    φ Q 𝒯 hQ hT

end Unramified

end Langlands.BruhatTits.IntegralModels
