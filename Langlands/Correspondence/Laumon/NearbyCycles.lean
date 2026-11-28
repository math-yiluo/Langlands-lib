import Langlands.Correspondence.Laumon.StrictTargetTrait
import WeilConjectures.SixFunctors.NearbyCycles.GaloisAction
import WeilConjectures.SixFunctors.NearbyCycles.HomComp
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology

/-!
# Nearby cycles on the strict target trait

Form the chart over the fixed strict target before adjoining the geometric generic field.
Exchange under model automorphisms gives the arithmetic transport of nearby cycles.
-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

open scoped CategoryTheory.Functor CategoryTheory.Obj

attribute [-instance] CategoryTheory.sfbRegularAbMonoidal CategoryTheory.sfbRegularAbSymmetric

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace Langlands.Henniart.Laumon

open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k]

section Points

variable (k)

/-- The generic point `Spec K^nr → S^nr` of the strict target trait. -/
abbrev strictTraitGenericPoint : Spec (.of (endUnramifiedField k)) ⟶ endStrictTrait k :=
  Spec.map (CommRingCat.ofHom (endStrictRing k).subtype)

/-- The special point `Spec (R^nr/(t)) → S^nr` of the strict target trait. -/
abbrev strictTraitSpecialPoint : Spec (.of (strictResidueRing k)) ⟶ endStrictTrait k :=
  Spec.map (CommRingCat.ofHom (strictResidue k))

end Points

section Chart

variable {A : Type u} [CommRing A] (ι : A →+* endStrictRing k) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A))

/-- The chart `X^nr = X ×_S S^nr` over the strict target trait. -/
abbrev strictChart : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom ι))

/-- The projection `X^nr → X`. -/
abbrev strictChartProjection : strictChart ι f ⟶ X :=
  pullback.fst _ _

/-- The structure map `X^nr → S^nr`. -/
abbrev strictChartStructure : strictChart ι f ⟶ endStrictTrait k :=
  pullback.snd _ _

/-- The generic fibre `X^nr ×_{S^nr} Spec K^nr`. -/
abbrev strictChartGeneric : Scheme.{u} :=
  pullback (strictChartStructure ι f) (strictTraitGenericPoint k)

/-- The special fibre `X^nr ×_{S^nr} Spec (R^nr/(t))`. -/
abbrev strictChartSpecial : Scheme.{u} :=
  pullback (strictChartStructure ι f) (strictTraitSpecialPoint k)

/-- The model of `X^nr` over the strict trait with generic fibre over `K^nr`. -/
def strictChartModel : NearbyCyclesModel (strictChart ι f) (strictChartSpecial ι f) where
  total := strictChart ι f
  generic := strictChartGeneric ι f
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := pullback.fst _ _

/-- The map of the generic fibre over `K^nr` to `Spec K^nr`. -/
abbrev strictChartGenericPoint : strictChartGeneric ι f ⟶
    Spec (.of (endUnramifiedField k)) :=
  pullback.snd (strictChartStructure ι f) (strictTraitGenericPoint k)

/-- The geometric generic fibre `(X^nr ×_{S^nr} Spec K^nr) ×_{K^nr} Spec Ω_s`. -/
abbrev traitNearbyGeneric : Scheme.{u} :=
  pullback (strictChartGenericPoint ι f)
    (Spec.map (CommRingCat.ofHom (algebraMap (endUnramifiedField k) (endGenericClosure k))))

/-- The nearby-cycles model of the chart. -/
def traitNearbyModel : NearbyCyclesModel (strictChart ι f) (strictChartSpecial ι f) :=
  (strictChartModel ι f).galoisLayer (strictChartGenericPoint ι f) (endGenericClosure k)

end Chart

section RationalPoint

variable {X : Scheme.{u}} {f : X ⟶ Spec (.of (endRing k))}

/-- The canonical lift of a rational special point to the strict special fibre. -/
def rationalStrictChartPoint (x₀ : Spec (.of k) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (endResidue k))) :
    Spec (.of (strictResidueRing k)) ⟶ strictChartSpecial (endStrictRingHom k) f :=
  let a := Spec.map (CommRingCat.ofHom (strictResidueBaseHom k)) ≫ x₀
  have ha : a ≫ f = strictTraitSpecialPoint k ≫
      Spec.map (CommRingCat.ofHom (endStrictRingHom k)) :=
    (Category.assoc _ x₀ f).trans
      ((congrArg (Spec.map (CommRingCat.ofHom (strictResidueBaseHom k)) ≫ ·) hx₀).trans
        ((Spec.map_comp (CommRingCat.ofHom (endResidue k))
          (CommRingCat.ofHom (strictResidueBaseHom k))).symm.trans
          ((congrArg (fun h : endRing k →+* strictResidueRing k =>
            Spec.map (CommRingCat.ofHom h)) (strictResidue_comp_endStrictRingHom k).symm).trans
            (Spec.map_comp (CommRingCat.ofHom (endStrictRingHom k))
              (CommRingCat.ofHom (strictResidue k))))))
  pullback.lift (pullback.lift a (strictTraitSpecialPoint k) ha)
    (𝟙 (Spec (.of (strictResidueRing k))))
    ((pullback.lift_snd _ _ _).trans (Category.id_comp _).symm)

end RationalPoint

section Galois

variable {A : Type u} [CommRing A] {ι : A →+* endStrictRing k} {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)}

/-- The automorphism of the strict target trait induced by `σ`. -/
abbrev strictTraitGalois (σ : Gal(endGenericClosure k/endField k)) :
    endStrictTrait k ⟶ endStrictTrait k :=
  Spec.map (CommRingCat.ofHom (strictRingGalois σ))

theorem strictTraitGalois_comp (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    strictTraitGalois σ ≫ Spec.map (CommRingCat.ofHom ι) = Spec.map (CommRingCat.ofHom ι) := by
  rw [strictTraitGalois, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]

theorem strictTraitGenericPoint_galois (σ : Gal(endGenericClosure k/endField k)) :
    strictTraitGenericPoint k ≫ strictTraitGalois σ =
      Spec.map (CommRingCat.ofHom (unramifiedGalois σ)) ≫ strictTraitGenericPoint k := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem strictTraitSpecialPoint_galois (σ : Gal(endGenericClosure k/endField k)) :
    strictTraitSpecialPoint k ≫ strictTraitGalois σ =
      Spec.map (CommRingCat.ofHom
        (strictResidueGalois σ : strictResidueRing k →+* strictResidueRing k)) ≫
        strictTraitSpecialPoint k :=
  (strictTargetTraitAut σ).comm_i.symm

theorem unramifiedGalois_algebraMap (σ : Gal(endGenericClosure k/endField k)) :
    Spec.map (CommRingCat.ofHom (algebraMap (endUnramifiedField k) (endGenericClosure k))) ≫
        Spec.map (CommRingCat.ofHom (unramifiedGalois σ)) =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (endUnramifiedField k) (endGenericClosure k))) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (f) in
/-- The automorphism `id_X × σ` of the chart `X^nr`. -/
def strictChartGalois (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) : strictChart ι f ⟶ strictChart ι f :=
  pullback.map _ _ _ _ (𝟙 X) (strictTraitGalois σ) (𝟙 _) (by simp)
    (by rw [Category.comp_id, strictTraitGalois_comp σ hσ])

variable (f) in
/-- The automorphism of the generic fibre over `K^nr`. -/
def strictChartGenericGalois (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) : strictChartGeneric ι f ⟶ strictChartGeneric ι f :=
  pullback.map _ _ _ _ (strictChartGalois f σ hσ)
    (Spec.map (CommRingCat.ofHom (unramifiedGalois σ))) (strictTraitGalois σ)
    (by simp [strictChartGalois]) (strictTraitGenericPoint_galois σ)

variable (f) in
/-- The automorphism of the special fibre. -/
def strictChartSpecialGalois (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) : strictChartSpecial ι f ⟶ strictChartSpecial ι f :=
  pullback.map _ _ _ _ (strictChartGalois f σ hσ)
    (Spec.map (CommRingCat.ofHom
      (strictResidueGalois σ : strictResidueRing k →+* strictResidueRing k)))
    (strictTraitGalois σ)
    (by simp [strictChartGalois]) (strictTraitSpecialPoint_galois σ)

variable (f) in
/-- The automorphism of the geometric generic fibre. -/
def traitNearbyGenericGalois (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    traitNearbyGeneric ι f ⟶ traitNearbyGeneric ι f :=
  pullback.map _ _ _ _ (strictChartGenericGalois f σ hσ)
    (Spec.map (CommRingCat.ofHom σ.toRingHom))
    (Spec.map (CommRingCat.ofHom (unramifiedGalois σ)))
    (pullback.lift_snd _ _ _).symm (unramifiedGalois_algebraMap σ)

theorem strictChartGenericGalois_fst (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    strictChartGenericGalois f σ hσ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ strictChartGalois f σ hσ :=
  pullback.lift_fst _ _ _

theorem strictChartSpecialGalois_fst (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    strictChartSpecialGalois f σ hσ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ strictChartGalois f σ hσ :=
  pullback.lift_fst _ _ _

theorem traitNearbyGenericGalois_fst (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    traitNearbyGenericGalois f σ hσ ≫
        pullback.fst (strictChartGenericPoint ι f)
          (Spec.map (CommRingCat.ofHom (algebraMap (endUnramifiedField k) (endGenericClosure k)))) =
      pullback.fst _ _ ≫ strictChartGenericGalois f σ hσ :=
  pullback.lift_fst _ _ _

theorem traitNearbyGenericGalois_comm (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    traitNearbyGenericGalois f σ hσ ≫ (traitNearbyModel ι f).j =
      (traitNearbyModel ι f).j ≫ strictChartGalois f σ hσ := by
  change traitNearbyGenericGalois f σ hσ ≫
      (pullback.fst (strictChartGenericPoint ι f)
          (Spec.map (CommRingCat.ofHom (algebraMap (endUnramifiedField k) (endGenericClosure k)))) ≫
        pullback.fst (strictChartStructure ι f) (strictTraitGenericPoint k)) =
    (pullback.fst (strictChartGenericPoint ι f)
          (Spec.map (CommRingCat.ofHom (algebraMap (endUnramifiedField k) (endGenericClosure k)))) ≫
        pullback.fst (strictChartStructure ι f) (strictTraitGenericPoint k)) ≫
      strictChartGalois f σ hσ
  rw [reassoc_of% traitNearbyGenericGalois_fst, strictChartGenericGalois_fst, Category.assoc]

variable (f) in
/-- The automorphism of the nearby-cycles model induced by `σ`. -/
def traitNearbyModelGalois (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    (traitNearbyModel ι f).Hom (traitNearbyModel ι f) (strictChartGalois f σ hσ)
      (strictChartSpecialGalois f σ hσ) where
  total := strictChartGalois f σ hσ
  generic := traitNearbyGenericGalois f σ hσ
  comm_j := traitNearbyGenericGalois_comm σ hσ
  comm_i := strictChartSpecialGalois_fst σ hσ
  comm_ε := traitNearbyGenericGalois_comm σ hσ

end Galois

theorem rationalStrictChartPoint_galois {X : Scheme.{u}} {f : X ⟶ Spec (.of (endRing k))}
    (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (endResidue k)))
    (σ : Gal(endGenericClosure k/endField k)) :
    rationalStrictChartPoint x₀ hx₀ ≫
        strictChartSpecialGalois f σ (strictRingGalois_comp_endStrictRingHom σ) =
      Spec.map (CommRingCat.ofHom (strictResidueGalois (k := k) σ)) ≫
        rationalStrictChartPoint x₀ hx₀ := by
  apply pullback.hom_ext
  · simp only [rationalStrictChartPoint, strictChartSpecialGalois, pullback.map,
      Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
    apply pullback.hom_ext
    · have hs : Spec.map (CommRingCat.ofHom (strictResidueGalois (k := k) σ)) ≫
          Spec.map (CommRingCat.ofHom (strictResidueBaseHom k)) =
            Spec.map (CommRingCat.ofHom (strictResidueBaseHom k)) :=
        (Spec.map_comp (CommRingCat.ofHom (strictResidueBaseHom k))
          (CommRingCat.ofHom (strictResidueGalois (k := k) σ))).symm.trans
          (congrArg (fun h : k →+* strictResidueRing k => Spec.map (CommRingCat.ofHom h))
            (strictResidueGalois_comp_baseHom σ))
      simpa only [strictChartGalois, pullback.map, Category.assoc, pullback.lift_fst_assoc,
        pullback.lift_fst, Category.comp_id] using congrArg (· ≫ x₀) hs.symm
    · simp only [strictChartGalois, pullback.map, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_snd, strictTraitSpecialPoint_galois]
  · simp only [rationalStrictChartPoint, strictChartSpecialGalois, pullback.map,
      Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]

section Action

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {A : Type u} [CommRing A] {ι : A →+* endStrictRing k} {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)}

theorem strictChartGalois_projection (σ : Gal(endGenericClosure k/endField k))
    (hσ : (strictRingGalois σ).comp ι = ι) :
    strictChartGalois f σ hσ ≫ strictChartProjection ι f = strictChartProjection ι f :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

variable (ι f) in
/-- The pullback `B^nr` of a complex on `X` to `X^nr`. -/
abbrev strictChartPullback
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (strictChart ι f)) Ab.{u + 1})
      (condensedRingObj Λ (strictChart ι f))) :=
  L((strictChartProjection ι f)^*⟦Λ⟧).obj B

variable (ι f) in
/-- The nearby cycles `Ψ(B^nr)` of the chart. -/
abbrev chartNearbyCycles
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (strictChartSpecial ι f)) Ab.{u + 1})
      (condensedRingObj Λ (strictChartSpecial ι f))) :=
  ((traitNearbyModel ι f).nearbyCycles Λ).obj (strictChartPullback Λ ι f B)

variable (f) in
/-- The action of `σ` on the nearby cycles. -/
def nearbyCyclesAction
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (σ : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι) :
    L((strictChartSpecialGalois f σ hσ)^*⟦Λ⟧).obj (chartNearbyCycles Λ ι f B) ⟶
      chartNearbyCycles Λ ι f B :=
  ((traitNearbyModelGalois f σ hσ).pullbackExchange Λ).app (strictChartPullback Λ ι f B) ≫
    ((traitNearbyModel ι f).nearbyCycles Λ).map
      ((leftDerivedUpperStarCompOfEq Λ (strictChartGalois_projection σ hσ)).inv.app B)

/-- The stalk at a geometric point. -/
def arithmeticNearbyStalk
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {F : Type u} [CommRing F] (x : Spec (.of F) ⟶ strictChartSpecial ι f) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of F))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of F)))) :=
  L((x)^*⟦Λ⟧).obj (chartNearbyCycles Λ ι f B)

/-- Arithmetic transport from the translated point back to the original point. -/
def arithmeticNearbyStalkMove
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {F : Type u} [CommRing F] (x : Spec (.of F) ⟶ strictChartSpecial ι f)
    (σ : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι) :
    arithmeticNearbyStalk Λ B (x ≫ strictChartSpecialGalois f σ hσ) ⟶
      arithmeticNearbyStalk Λ B x :=
  (leftDerivedUpperStarComp Λ x (strictChartSpecialGalois f σ hσ)).hom.app _ ≫
    L((x)^*⟦Λ⟧).map (nearbyCyclesAction Λ f B σ hσ)

/-- The semilinear transport on the stalk. -/
def arithmeticNearbyStalkTransport
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {F : Type u} [CommRing F] (x : Spec (.of F) ⟶ strictChartSpecial ι f)
    (σ : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι)
    (τ : F →+* F) (hx : x ≫ strictChartSpecialGalois f σ hσ = Spec.map (CommRingCat.ofHom τ) ≫ x) :
    L((Spec.map (CommRingCat.ofHom τ))^*⟦Λ⟧).obj (arithmeticNearbyStalk Λ B x) ⟶
      arithmeticNearbyStalk Λ B x :=
  (leftDerivedUpperStarComp Λ (Spec.map (CommRingCat.ofHom τ)) x).inv.app _ ≫
    eqToHom (congrArg (arithmeticNearbyStalk Λ B) hx.symm) ≫
    arithmeticNearbyStalkMove Λ B x σ hσ

/-- The derived direct image of the stalk to `Spec ℤ`. -/
def arithmeticNearbyStalkSections
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {F : Type u} [CommRing F] (x : Spec (.of F) ⟶ strictChartSpecial ι f) :
    DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology specZ) Ab.{u + 1})
      (condensedRingObj Λ specZ)) :=
  R((toSpecZ (Spec (.of F)))_*⟦Λ⟧).obj (arithmeticNearbyStalk Λ B x)

/-- The coefficient complex of the stalk. -/
abbrev arithmeticNearbyStalkComplex
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {F : Type u} [CommRing F] (x : Spec (.of F) ⟶ strictChartSpecial ι f) :=
  (condensedRingCoefficientSections Λ specZ).rightDerivedFunctor.obj
    (arithmeticNearbyStalkSections Λ B x)

/-- The action of `σ` on the coefficient complex of the stalk. -/
def arithmeticNearbyStalkAction
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {F : Type u} [CommRing F] (x : Spec (.of F) ⟶ strictChartSpecial ι f)
    (σ : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι)
    (τ : F →+* F) (hx : x ≫ strictChartSpecialGalois f σ hσ = Spec.map (CommRingCat.ofHom τ) ≫ x) :
    arithmeticNearbyStalkComplex Λ B x ⟶ arithmeticNearbyStalkComplex Λ B x :=
  (condensedRingCoefficientSections Λ specZ).rightDerivedFunctor.map
    ((derivedUpperStarLowerStarAdjunction Λ (toSpecZ (Spec (.of F)))).homEquiv _ _
      ((leftDerivedUpperStarCompOfEq Λ (comp_toSpecZ (Spec.map (CommRingCat.ofHom τ)))).hom.app
          (arithmeticNearbyStalkSections Λ B x) ≫
        L((Spec.map (CommRingCat.ofHom τ))^*⟦Λ⟧).map
          ((derivedUpperStarLowerStarAdjunction Λ (toSpecZ (Spec (.of F)))).counit.app
            (arithmeticNearbyStalk Λ B x)) ≫
        arithmeticNearbyStalkTransport Λ B x σ hσ τ hx))

end Action

section RationalAction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X : Scheme.{u}} {f : X ⟶ Spec (.of (endRing k))}

/-- The full arithmetic Galois action on the sections of the stalk at the lift of a rational
special point. -/
def rationalNearbyStalkAction
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (endResidue k)))
    (σ : Gal(endGenericClosure k/endField k)) :
    arithmeticNearbyStalkComplex (ι := endStrictRingHom k) (f := f) Λ B
        (F := strictResidueRing k) (rationalStrictChartPoint (f := f) x₀ hx₀) ⟶
      arithmeticNearbyStalkComplex (ι := endStrictRingHom k) (f := f) Λ B
        (F := strictResidueRing k) (rationalStrictChartPoint (f := f) x₀ hx₀) :=
  arithmeticNearbyStalkAction (ι := endStrictRingHom k) (f := f) Λ B (F := strictResidueRing k)
    (rationalStrictChartPoint (f := f) x₀ hx₀) σ (strictRingGalois_comp_endStrictRingHom σ)
    (strictResidueGalois (k := k) σ) (rationalStrictChartPoint_galois x₀ hx₀ σ)

end RationalAction

section Statements

/-- An element of the inertia group as an automorphism of `Ω_s` over `K^nr`. -/
def inertiaGalois (σ : Gal(endGenericClosure k/endField k))
    (hσ : σ ∈ (endUnramifiedField k).fixingSubgroup) :
    endGenericClosure k ≃ₐ[endUnramifiedField k] endGenericClosure k :=
  IntermediateField.fixingSubgroupEquiv (endUnramifiedField k) ⟨σ, hσ⟩

variable {A : Type u} [CommRing A] (ι : A →+* endStrictRing k) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A))

/-- The geometric point of `X^nr` under a geometric point of the special fibre. -/
abbrev strictChartPoint {F : Type u} [Field F] (x : Spec (.of F) ⟶ strictChartSpecial ι f) :
    Spec (.of F) ⟶ strictChart ι f :=
  x ≫ pullback.fst _ _

/-- The generic fibre of the strict localization. -/
abbrev strictLocalGenericFibre {F : Type u} [Field F] [IsSepClosed F]
    (x : Spec (.of F) ⟶ strictChartSpecial ι f) : Scheme.{u} :=
  pullback (Scheme.strictLocalizationToBase (strictChartPoint ι f x)) (traitNearbyModel ι f).j

/-- Its map to `X^nr`. -/
abbrev strictLocalGenericFibreMap {F : Type u} [Field F] [IsSepClosed F]
    (x : Spec (.of F) ⟶ strictChartSpecial ι f) :
    strictLocalGenericFibre ι f x ⟶ strictChart ι f :=
  pullback.fst _ _ ≫ Scheme.strictLocalizationToBase (strictChartPoint ι f x)

end Statements

section StalkFormula

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {A : Type u} [CommRing A] {ι : A →+* endStrictRing k} {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
  {F : Type u} [Field F] [IsSepClosed F] (x : Spec (.of F) ⟶ strictChartSpecial ι f)

/-- The closed geometric point of the strict localization. -/
abbrev strictLocalClosedPoint : Spec (.of F) ⟶ Scheme.strictLocalization (strictChartPoint ι f x) :=
  Spec.map (Scheme.strictHenselizationEval (strictChartPoint ι f x))

/-- The map from the generic fibre into the strict localization. -/
abbrev strictLocalGenericInclusion :
    strictLocalGenericFibre ι f x ⟶ Scheme.strictLocalization (strictChartPoint ι f x) :=
  pullback.fst _ _

variable (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X)))

/-- The restriction of the arithmetic complex to the strict-local generic fibre. -/
abbrev strictLocalGenericInput :=
  L((strictLocalGenericFibreMap ι f x)^*⟦Λ⟧).obj (strictChartPullback Λ ι f B)

/-- Derived sections on the strict-local generic fibre. -/
abbrev strictLocalGenericCohomology :=
  (condensedRingOrdinaryCoefficientComplex Λ (toSpecZ (strictLocalGenericFibre ι f x))).obj
    (strictLocalGenericInput Λ x B)

/-- The stalk of the local generic direct image at the closed point of the strict localization. -/
abbrev strictLocalNearbyGerm :=
  L((strictLocalClosedPoint x)^*⟦Λ⟧).obj
    (R((strictLocalGenericInclusion x)_*⟦Λ⟧).obj (strictLocalGenericInput Λ x B))

/-- The canonical restriction of the nearby stalk to the germ on the strict localization. -/
def strictNearbyStalkRestriction :
    arithmeticNearbyStalk Λ B x ⟶ strictLocalNearbyGerm Λ x B :=
  let M := traitNearbyModel ι f
  let p := Scheme.strictLocalizationToBase (strictChartPoint ι f x)
  let a := strictLocalGenericInclusion x
  let b := pullback.snd p M.j
  let s := strictLocalClosedPoint x
  have hs : s ≫ p = x ≫ M.i :=
    Scheme.spec_map_strictHenselizationEval_comp_strictLocalizationToBase (strictChartPoint ι f x)
  have sq : CommSq b a M.j p := ⟨pullback.condition.symm⟩
  let K := strictChartPullback Λ ι f B
  (leftDerivedUpperStarComp Λ x M.i).inv.app _ ≫
    (leftDerivedUpperStarCompOfEq Λ hs).hom.app _ ≫
    L((s)^*⟦Λ⟧).map ((baseChangeMap Λ sq).app (L((M.ε)^*⟦Λ⟧).obj K)) ≫
    L((s)^*⟦Λ⟧).map
      (R((a)_*⟦Λ⟧).map ((leftDerivedUpperStarCompOfEq Λ sq.w).inv.app K))

/-- The germ map from cohomology on the strict-local generic fibre. -/
def strictLocalNearbyGermMap :
    strictLocalGenericCohomology Λ x B ⟶
      (condensedRingOrdinaryCoefficientComplex Λ (toSpecZ (Spec (.of F)))).obj
        (strictLocalNearbyGerm Λ x B) :=
  let a := strictLocalGenericInclusion x
  let s := strictLocalClosedPoint x
  let K := strictLocalGenericInput Λ x B
  let adj := derivedUpperStarLowerStarAdjunction Λ (toSpecZ (strictLocalGenericFibre ι f x))
  let h := (derivedUpperStarLowerStarAdjunction Λ a).homEquiv _ _
    ((leftDerivedUpperStarCompOfEq Λ (comp_toSpecZ a)).inv.app _ ≫ adj.counit.app K)
  (condensedRingCoefficientSections Λ specZ).rightDerivedFunctor.map
    ((derivedUpperStarLowerStarAdjunction Λ (toSpecZ (Spec (.of F)))).homEquiv _ _
      ((leftDerivedUpperStarCompOfEq Λ (comp_toSpecZ s)).hom.app _ ≫ L((s)^*⟦Λ⟧).map h))

end StalkFormula

/-- The finite-coefficient strict-local formula for nearby stalks of bounded below complexes
of étale origin. -/
def StrictNearbyStalkFormulaStatement : Prop :=
  ∀ (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
    [Finite T] (k : Type u) [Field k] [Finite k], IsUnit (ringChar k : T) →
    ∀ (A : Type u) [CommRing A] (ι : A →+* endStrictRing k) (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))),
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) _
        ((finiteCoefficientDerivedEquivalence _ T).functor.obj B) →
    ∀ (F : Type u) [Field F] [IsSepClosed F] (x : Spec (.of F) ⟶ strictChartSpecial ι f),
      IsIso (strictNearbyStalkRestriction (Profinite.continuousMapRingObj T) x B) ∧
        IsIso (strictLocalNearbyGermMap (Profinite.continuousMapRingObj T) x B)

/-- The coefficient complex at the lift of a rational point has the full arithmetic action. -/
def RationalNearbyStalkGaloisStatement : Prop :=
  ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of (endRing k)))
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (endResidue k))),
    rationalNearbyStalkAction (f := f) Λ B x₀ hx₀ (1 : Gal(endGenericClosure k/endField k)) =
        𝟙 _ ∧
      ∀ σ τ : Gal(endGenericClosure k/endField k),
        rationalNearbyStalkAction (f := f) Λ B x₀ hx₀ (σ * τ) =
          rationalNearbyStalkAction (f := f) Λ B x₀ hx₀ τ ≫
            rationalNearbyStalkAction (f := f) Λ B x₀ hx₀ σ

/-- Arithmetic transport is invertible and satisfies the unit and composition laws. On inertia
it agrees with the Galois-layer action. The laws also hold on the stalk at a point equipped with
compatible field maps. -/
def NearbyStalkGaloisStatement : Prop :=
  RationalNearbyStalkGaloisStatement.{u} ∧
  ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] (A : Type u) [CommRing A] (ι : A →+* endStrictRing k)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))),
    (∀ (σ : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι),
      IsIso (nearbyCyclesAction Λ f B σ hσ)) ∧
    (∀ h1 : (strictRingGalois (1 : Gal(endGenericClosure k/endField k))).comp ι = ι,
      ∃ e : strictChartSpecialGalois f (1 : Gal(endGenericClosure k/endField k)) h1 = 𝟙 _,
        nearbyCyclesAction Λ f B (1 : Gal(endGenericClosure k/endField k)) h1 =
          eqToHom (congrArg (fun g => (L((g)^*⟦Λ⟧)).obj (chartNearbyCycles Λ ι f B)) e) ≫
            (leftDerivedUpperStarId Λ _).hom.app _) ∧
    (∀ (σ σ' : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι)
        (hσ' : (strictRingGalois σ').comp ι = ι) (hσσ' : (strictRingGalois (σ * σ')).comp ι = ι),
      ∃ e : strictChartSpecialGalois f σ hσ ≫ strictChartSpecialGalois f σ' hσ' =
          strictChartSpecialGalois f (σ * σ') hσσ',
        nearbyCyclesAction Λ f B (σ * σ') hσσ' =
          (leftDerivedUpperStarCompOfEq Λ e).hom.app _ ≫
            L((strictChartSpecialGalois f σ hσ)^*⟦Λ⟧).map (nearbyCyclesAction Λ f B σ' hσ') ≫
            nearbyCyclesAction Λ f B σ hσ) ∧
    (∀ (σ : Gal(endGenericClosure k/endField k))
        (hI : σ ∈ (endUnramifiedField k).fixingSubgroup) (hσ : (strictRingGalois σ).comp ι = ι),
      ∃ e : strictChartSpecialGalois f σ hσ = 𝟙 _,
        nearbyCyclesAction Λ f B σ hσ =
          eqToHom (congrArg (fun g => (L((g)^*⟦Λ⟧)).obj (chartNearbyCycles Λ ι f B)) e) ≫
            (leftDerivedUpperStarId Λ _).hom.app _ ≫
            (strictChartModel ι f).galoisLayerAction Λ (strictChartGenericPoint ι f)
              (endGenericClosure k) (inertiaGalois σ hI) (strictChartPullback Λ ι f B)) ∧
    (∀ (B' : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))) (g : B ⟶ B') (σ : Gal(endGenericClosure k/endField k))
        (hσ : (strictRingGalois σ).comp ι = ι),
      nearbyCyclesAction Λ f B σ hσ ≫ ((traitNearbyModel ι f).nearbyCycles Λ).map
          (L((strictChartProjection ι f)^*⟦Λ⟧).map g) =
        L((strictChartSpecialGalois f σ hσ)^*⟦Λ⟧).map (((traitNearbyModel ι f).nearbyCycles Λ).map
          (L((strictChartProjection ι f)^*⟦Λ⟧).map g)) ≫ nearbyCyclesAction Λ f B' σ hσ) ∧
    ∀ (F : Type u) [CommRing F] (x : Spec (.of F) ⟶ strictChartSpecial ι f),
      (∀ (σ : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι),
        IsIso (arithmeticNearbyStalkMove Λ B x σ hσ)) ∧
      (∀ (σ σ' : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι)
          (hσ' : (strictRingGalois σ').comp ι = ι)
          (hσσ' : (strictRingGalois (σ * σ')).comp ι = ι) (τ τ' : F →+* F)
          (hx : x ≫ strictChartSpecialGalois f σ hσ = Spec.map (CommRingCat.ofHom τ) ≫ x)
          (hx' : x ≫ strictChartSpecialGalois f σ' hσ' = Spec.map (CommRingCat.ofHom τ') ≫ x)
          (hxx' : x ≫ strictChartSpecialGalois f (σ * σ') hσσ' =
            Spec.map (CommRingCat.ofHom (τ.comp τ')) ≫ x),
        ∃ e : Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom τ') =
            Spec.map (CommRingCat.ofHom (τ.comp τ')),
          arithmeticNearbyStalkTransport Λ B x (σ * σ') hσσ' (τ.comp τ') hxx' =
              (leftDerivedUpperStarCompOfEq Λ e).hom.app _ ≫
                L((Spec.map (CommRingCat.ofHom τ))^*⟦Λ⟧).map
                  (arithmeticNearbyStalkTransport Λ B x σ' hσ' τ' hx') ≫
                arithmeticNearbyStalkTransport Λ B x σ hσ τ hx ∧
            arithmeticNearbyStalkAction Λ B x (σ * σ') hσσ' (τ.comp τ') hxx' =
              arithmeticNearbyStalkAction Λ B x σ' hσ' τ' hx' ≫
                arithmeticNearbyStalkAction Λ B x σ hσ τ hx) ∧
      ∀ (h1 : (strictRingGalois (1 : Gal(endGenericClosure k/endField k))).comp ι = ι)
        (hx1 : x ≫ strictChartSpecialGalois f (1 : Gal(endGenericClosure k/endField k)) h1 =
          Spec.map (CommRingCat.ofHom (RingHom.id F)) ≫ x),
        arithmeticNearbyStalkAction Λ B x (1 : Gal(endGenericClosure k/endField k)) h1
          (RingHom.id F) hx1 = 𝟙 _

end Langlands.Henniart.Laumon
