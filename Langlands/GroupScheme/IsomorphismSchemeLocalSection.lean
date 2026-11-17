import Langlands.GroupScheme.IsomorphismSchemeActionTransport
import Langlands.GroupScheme.OuterIsomorphismNormalizedSection
import Langlands.GroupScheme.SchemeActionParameterSection

/-! # Local orbit sections expressed over the original base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalSectionBase

variable {S U : Scheme.{u}} (b : U ⟶ S)

/-- Regard the structure map of an object over the local base as a relative morphism. -/
def projection (Q : Over U) : (Over.map b).obj Q ⟶ Over.mk b :=
  Over.homMk Q.hom rfl

@[simp] theorem map_projection {Q Q' : Over U} (f : Q ⟶ Q') :
    (Over.map b).map f ≫ projection b Q' = projection b Q := by
  apply Over.OverMorphism.ext
  exact Over.w f

/-- The actual pullback parameter is the product with the local base in the old slice. -/
def tensorParameterIso (X : Over S) :
    (Over.map b).obj ((Over.pullback b).obj X) ≅ X ⊗ Over.mk b :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (pullback.fst X.hom b ≫ X.hom) =
      pullback.snd X.hom b ≫ b
    rw [Category.id_comp, pullback.condition])

@[simp] theorem tensorParameterIso_hom_fst (X : Over S) :
    (tensorParameterIso b X).hom ≫ fst X (Over.mk b) =
      (Over.mapPullbackAdj b).counit.app X := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

@[simp] theorem tensorParameterIso_hom_snd (X : Over S) :
    (tensorParameterIso b X).hom ≫ snd X (Over.mk b) =
      projection b ((Over.pullback b).obj X) := by
  apply Over.OverMorphism.ext
  exact Category.id_comp _

/-- Pulling back one factor and then forgetting the local base gives the expected product. -/
def tensorProductIso (X : Over S) (Q : Over U) :
    (Over.map b).obj (((Over.pullback b).obj X) ⊗ Q) ≅ X ⊗ (Over.map b).obj Q :=
  Over.isoMk (pullbackLeftPullbackSndIso X.hom b Q.hom) (by
    change (pullbackLeftPullbackSndIso X.hom b Q.hom).hom ≫
        (pullback.fst X.hom (Q.hom ≫ b) ≫ X.hom) =
      (pullback.fst (pullback.snd X.hom b) Q.hom ≫ pullback.snd X.hom b) ≫ b
    rw [← Category.assoc, pullbackLeftPullbackSndIso_hom_fst, Category.assoc,
      pullback.condition, ← Category.assoc])

@[simp] theorem tensorProductIso_hom_fst (X : Over S) (Q : Over U) :
    (tensorProductIso b X Q).hom ≫ fst X ((Over.map b).obj Q) =
      (Over.map b).map (fst ((Over.pullback b).obj X) Q) ≫
        (Over.mapPullbackAdj b).counit.app X := by
  apply Over.OverMorphism.ext
  exact pullbackLeftPullbackSndIso_hom_fst X.hom b Q.hom

@[simp] theorem tensorProductIso_hom_snd (X : Over S) (Q : Over U) :
    (tensorProductIso b X Q).hom ≫ snd X ((Over.map b).obj Q) =
      (Over.map b).map (snd ((Over.pullback b).obj X) Q) := by
  apply Over.OverMorphism.ext
  exact pullbackLeftPullbackSndIso_hom_snd X.hom b Q.hom

/-- Compare the chosen monoidal product with the categorical binary product. -/
def tensorToProd {V : Scheme.{u}} (X Y : Over V) : X ⊗ Y ≅ X ⨯ Y :=
  IsLimit.conePointUniqueUpToIso (tensorProductIsBinaryProduct X Y) (limit.isLimit (pair X Y))

@[simp] theorem tensorToProd_hom_fst {V : Scheme.{u}} (X Y : Over V) :
    (tensorToProd X Y).hom ≫ prod.fst = fst X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (tensorProductIsBinaryProduct X Y) (limit.isLimit (pair X Y))
      (Discrete.mk WalkingPair.left)

@[simp] theorem tensorToProd_hom_snd {V : Scheme.{u}} (X Y : Over V) :
    (tensorToProd X Y).hom ≫ prod.snd = snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (tensorProductIsBinaryProduct X Y) (limit.isLimit (pair X Y))
      (Discrete.mk WalkingPair.right)

/-- Express the actual pullback parameter as a categorical product over the old base. -/
def parameterIso (X : Over S) :
    (Over.map b).obj ((Over.pullback b).obj X) ≅ X ⨯ Over.mk b :=
  tensorParameterIso b X ≪≫ tensorToProd X (Over.mk b)

@[simp] theorem parameterIso_hom_fst (X : Over S) :
    (parameterIso b X).hom ≫ prod.fst = (Over.mapPullbackAdj b).counit.app X := by
  simp only [parameterIso, Iso.trans_hom, Category.assoc,
    tensorToProd_hom_fst, tensorParameterIso_hom_fst]

@[simp] theorem parameterIso_hom_snd (X : Over S) :
    (parameterIso b X).hom ≫ prod.snd =
      projection b ((Over.pullback b).obj X) := by
  simp only [parameterIso, Iso.trans_hom, Category.assoc,
    tensorToProd_hom_snd, tensorParameterIso_hom_snd]

/-- Express the iterated pullback product as a categorical product over the old base. -/
def productIso (X : Over S) (Q : Over U) :
    (Over.map b).obj (((Over.pullback b).obj X) ⊗ Q) ≅ X ⨯ (Over.map b).obj Q :=
  tensorProductIso b X Q ≪≫ tensorToProd X ((Over.map b).obj Q)

@[simp] theorem productIso_hom_fst (X : Over S) (Q : Over U) :
    (productIso b X Q).hom ≫ prod.fst =
      (Over.map b).map (fst ((Over.pullback b).obj X) Q) ≫
        (Over.mapPullbackAdj b).counit.app X := by
  simp only [productIso, Iso.trans_hom, Category.assoc,
    tensorToProd_hom_fst, tensorProductIso_hom_fst]

@[reassoc (attr := simp)] theorem productIso_hom_snd (X : Over S) (Q : Over U) :
    (productIso b X Q).hom ≫ prod.snd =
      (Over.map b).map (snd ((Over.pullback b).obj X) Q) := by
  simp only [productIso, Iso.trans_hom, Category.assoc,
    tensorToProd_hom_snd, tensorProductIso_hom_snd]

end LocalSectionBase

namespace GroupIsomorphismScheme

variable {S U : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G) (b : U ⟶ S)
  {Q : Over U} (s : Q ⟶ (I.baseChange b).parameter)

/-- Forget the local base of a supplied orbit section, retaining its original Isom parameter. -/
def localSection : (Over.map b).obj Q ⟶ I.parameter :=
  (Over.map b).map s ≫ (Over.mapPullbackAdj b).counit.app I.parameter

/-- The orbit map over the local base agrees with the parameter-preserving orbit map
over the original base after the canonical product comparisons. -/
theorem localSection_orbitMap :
    (LocalSectionBase.productIso b A.X Q).hom ≫
        (SchemeAction.parameterSectionMap (I.modObj a)
          (LocalSectionBase.projection b Q) (I.localSection b s)) =
      (Over.map b).map ((I.baseChange b).sectionOrbitMap (a.baseChange b) s) ≫
        (LocalSectionBase.parameterIso b I.parameter).hom := by
  let F : (Over.pullback b).obj A.X ⊗ Q ⟶ (Over.pullback b).obj I.parameter :=
    (I.baseChange b).sectionOrbitMap (a.baseChange b) s
  change (LocalSectionBase.productIso b A.X Q).hom ≫
      SchemeAction.parameterSectionMap (I.modObj a)
        (LocalSectionBase.projection b Q) (I.localSection b s) =
    (Over.map b).map F ≫ (LocalSectionBase.parameterIso b I.parameter).hom
  apply prod.hom_ext
  · simp only [Category.assoc, LocalSectionBase.parameterIso_hom_fst]
    have he := I.baseChange_actionHom b a
      (fst ((GroupScheme.baseChange b).obj A).X Q)
      (snd ((GroupScheme.baseChange b).obj A).X Q ≫ s)
    have ht := congrArg
      (((Over.mapPullbackAdj b).homEquiv
        (((GroupScheme.baseChange b).obj A).X ⊗ Q) I.parameter).symm) he
    rw [Equiv.symm_apply_apply] at ht
    change
      (Over.map b).map F ≫
          (Over.mapPullbackAdj b).counit.app I.parameter =
        lift ((Over.map b).map (fst ((Over.pullback b).obj A.X) Q) ≫
            (Over.mapPullbackAdj b).counit.app A.X)
          ((Over.map b).map (snd ((Over.pullback b).obj A.X) Q ≫ s) ≫
            (Over.mapPullbackAdj b).counit.app I.parameter) ≫ I.actionHom a at ht
    rw [ht]
    change (LocalSectionBase.productIso b A.X Q).hom ≫
        (prod.lift
          (SchemeAction.act (I.modObj a) prod.fst (prod.snd ≫ I.localSection b s))
          (prod.snd ≫ LocalSectionBase.projection b Q)) ≫ prod.fst = _
    simp only [prod.lift_fst, SchemeAction.naturality,
      LocalSectionBase.productIso_hom_fst, localSection,
      LocalSectionBase.productIso_hom_snd_assoc, Functor.map_comp]
    change lift _ _ ≫ I.actionHom a = _
    exact congrArg
      (fun z : (Over.map b).obj (((Over.pullback b).obj A.X) ⊗ Q) ⟶ I.parameter =>
        lift ((Over.map b).map (fst ((Over.pullback b).obj A.X) Q) ≫
          (Over.mapPullbackAdj b).counit.app A.X) z ≫ I.actionHom a)
      (Category.assoc ((Over.map b).map (snd ((Over.pullback b).obj A.X) Q))
        ((Over.map b).map s) ((Over.mapPullbackAdj b).counit.app I.parameter)).symm
  · simp only [Category.assoc, LocalSectionBase.parameterIso_hom_snd,
      LocalSectionBase.map_projection]
    change (LocalSectionBase.productIso b A.X Q).hom ≫
        (prod.lift
          (SchemeAction.act (I.modObj a) prod.fst (prod.snd ≫ I.localSection b s))
          (prod.snd ≫ LocalSectionBase.projection b Q)) ≫ prod.snd =
      LocalSectionBase.projection b (((Over.pullback b).obj A.X) ⊗ Q)
    simp only [prod.lift_snd, ← Category.assoc, LocalSectionBase.productIso_hom_snd,
      LocalSectionBase.map_projection]

variable (h : ∀ (T : Over U), Function.Bijective
  (fun z : (T ⟶ ((GroupScheme.baseChange b).obj A).X) × (T ⟶ Q) =>
    lift z.1 (z.2 ≫ s) ≫ (I.baseChange b).actionHom (a.baseChange b)))

include h in
/-- An all-test orbit section on the local base gives an isomorphism of the
parameter-preserving orbit family over the original base. -/
theorem localSection_isIso :
    IsIso (SchemeAction.parameterSectionMap (I.modObj a)
      (LocalSectionBase.projection b Q) (I.localSection b s)) := by
  let F : (Over.pullback b).obj A.X ⊗ Q ⟶ (Over.pullback b).obj I.parameter :=
    (I.baseChange b).sectionOrbitMap (a.baseChange b) s
  have : IsIso F := (I.baseChange b).sectionOrbitMap_isIso (a.baseChange b) s h
  have he := I.localSection_orbitMap a b s
  change (LocalSectionBase.productIso b A.X Q).hom ≫
      SchemeAction.parameterSectionMap (I.modObj a)
        (LocalSectionBase.projection b Q) (I.localSection b s) =
    (Over.map b).map F ≫ (LocalSectionBase.parameterIso b I.parameter).hom at he
  have hi : SchemeAction.parameterSectionMap (I.modObj a)
      (LocalSectionBase.projection b Q) (I.localSection b s) =
        (LocalSectionBase.productIso b A.X Q).inv ≫
          (Over.map b).map F ≫
            (LocalSectionBase.parameterIso b I.parameter).hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [hi]
  infer_instance

include h in
/-- The local orbit section yields the full bijection required by parameter-section descent. -/
theorem localSection_bijective (T : Over S) :
    Function.Bijective
      (fun z : (T ⟶ A.X) × (T ⟶ (Over.map b).obj Q) =>
        prod.lift (SchemeAction.act (I.modObj a) z.1 (z.2 ≫ I.localSection b s))
          (z.2 ≫ LocalSectionBase.projection b Q)) := by
  let F := SchemeAction.parameterSectionMap (I.modObj a)
    (LocalSectionBase.projection b Q) (I.localSection b s)
  let := I.localSection_isIso a b s h
  constructor
  · intro z z' he
    have hp : prod.lift z.1 z.2 ≫ F = prod.lift z'.1 z'.2 ≫ F := by
      simpa only [F, SchemeAction.parameterSectionMap_apply] using he
    have hz := (cancel_mono F).mp hp
    apply Prod.ext
    · simpa only [prod.lift_fst] using congrArg (fun f => f ≫ prod.fst) hz
    · simpa only [prod.lift_snd] using congrArg (fun f => f ≫ prod.snd) hz
  · intro p
    let v := p ≫ inv F
    refine ⟨(v ≫ prod.fst, v ≫ prod.snd), ?_⟩
    change prod.lift
        (SchemeAction.act (I.modObj a) (v ≫ prod.fst)
          ((v ≫ prod.snd) ≫ I.localSection b s))
        ((v ≫ prod.snd) ≫ LocalSectionBase.projection b Q) = p
    rw [← SchemeAction.parameterSectionMap_apply]
    change prod.lift (v ≫ prod.fst) (v ≫ prod.snd) ≫ F = p
    rw [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
    simp only [v, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end GroupIsomorphismScheme

end Langlands.GroupScheme
