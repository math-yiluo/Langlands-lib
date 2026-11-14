import Langlands.Geometry.FormalGroup.DeligneEtaQuotientBaseChange
import Langlands.Geometry.FormalGroup.DeligneTangentQuotientBaseChange

/-! # The actual stalk and Pi-quotient u squares under base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace

namespace Langlands.DeligneFormalSpace

/-- The actual structural stalk comparison sends a unit germ to the scalar-extension unit. -/
theorem structuralPullbackStalkIso_unit_germ {S S' : Scheme.{u}} (f : S' ⟶ S)
    (x : S') (M : S.Modules) (U : S.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    ((Langlands.AlgebraicGeometry.Modules.StalkPullback.pullbackStalkIso f x).app M).hom
        (TopCat.Presheaf.germ ((Scheme.Modules.pullback f).obj M).val.presheaf
          (f ⁻¹ᵁ U) x hx
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (.op U) m)) =
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
        ((Langlands.AlgebraicGeometry.Modules.stalkFunctor (f x)).obj M)
          (TopCat.Presheaf.germ M.val.presheaf U (f x) hx m) := by
  let A := ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Langlands.AlgebraicGeometry.Modules.StalkAdjunction.adjunction x)).ofNatIsoRight
      (Langlands.AlgebraicGeometry.Modules.StalkPullback.skyscraperPushforwardIso f x)
  let B := (Langlands.AlgebraicGeometry.Modules.StalkAdjunction.adjunction (f x)).comp
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app A B M
  simp only [Adjunction.homEquiv_unit] at h
  exact congrFun (congrArg (fun k => k.val.app (.op U) m) h) ⟨hx⟩

variable {O : Type u} [CommRing O] {X Y : TopCat.{u}}

/-- The comparison with sheafified presheaf pullback preserves the actual units. -/
theorem inverseImagePullbackIso_unit (f : X ⟶ Y) (M : Y.Sheaf (ModuleCat.{u} O)) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app M).hom ≫
        (TopCat.Presheaf.pushforward (ModuleCat.{u} O) f).map
          ((TopCat.Sheaf.pullbackIso (ModuleCat.{u} O) f).hom.app M).hom =
      (TopCat.Presheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app M.obj ≫
        (TopCat.Presheaf.pushforward (ModuleCat.{u} O) f).map
          (toSheafify (Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback (ModuleCat.{u} O) f).obj M.obj)) := by
  let A := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  let B := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) (ModuleCat.{u} O) (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app A B M
  simp only [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k.hom) h

/-- The existing inverse-image stalk comparison carries a germ to the actual unit germ. -/
theorem inverseImageStalkIso_germ (f : X ⟶ Y) (M : Y.Sheaf (ModuleCat.{u} O))
    (x : X) (U : Opens Y) (hx : f x ∈ U) :
    TopCat.Presheaf.germ M.obj U (f x) hx ≫ (inverseImageStalkIso f M x).hom =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app M).hom.app
        (.op U)) ≫
          (TopCat.Presheaf.germ ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M).obj
            ((Opens.map f).obj U) x hx) := by
  let P := TopCat.Presheaf.pullback (ModuleCat.{u} O) f
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x
  let e := (TopCat.Sheaf.pullbackIso (ModuleCat.{u} O) f).app M
  have h := congrArg (fun k => k.app (.op U)) (inverseImagePullbackIso_unit f M)
  change
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app M).hom.app
      (.op U)) ≫ e.hom.hom.app (.op ((Opens.map f).obj U)) =
    ((TopCat.Presheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app M.obj).app
      (.op U) ≫
        (toSheafify (Opens.grothendieckTopology X) (P.obj M.obj)).app
          (.op ((Opens.map f).obj U)) at h
  dsimp only [inverseImageStalkIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    Functor.mapIso_inv, Functor.comp_map]
  change TopCat.Presheaf.germ M.obj U (f x) hx ≫
      ((TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f M.obj x).hom ≫
        T.map (toSheafify (Opens.grothendieckTopology X) (P.obj M.obj)) ≫
        T.map e.inv.hom) = _
  rw [← Category.assoc, ← Category.assoc]
  change (TopCat.Presheaf.germ M.obj U (f x) hx ≫
    TopCat.Presheaf.stalkPullbackHom (ModuleCat.{u} O) f M.obj x) ≫ _ ≫ _ = _
  rw [TopCat.Presheaf.germ_stalkPullbackHom]
  rw [Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    ← Category.assoc, ← h, Category.assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  simp only [← Category.assoc, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, e.hom_inv_id]
  change (_ ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]

section ScalarUnits

variable {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']

/-- Naturality of the extension unit, on underlying elements. -/
theorem extendScalars_unit_map (ρ : R →+* R') {M N : ModuleCat.{u} R}
    (g : M ⟶ N) (m : M) :
    (ModuleCat.extendScalars ρ).map g
        ((ModuleCat.extendRestrictScalarsAdj ρ).unit.app M m) =
      (ModuleCat.extendRestrictScalarsAdj ρ).unit.app N (g m) :=
  (congrArg (fun k => k m) ((ModuleCat.extendRestrictScalarsAdj ρ).unit.naturality g)).symm

/-- Composition of scalar extension sends the composite unit to the two successive units. -/
theorem extendScalarsComp_unit (ρ : R →+* R') (σ : R' →+* R'')
    (M : ModuleCat.{u} R) (m : M) :
    ((ModuleCat.extendScalarsComp ρ σ).app M).hom
        ((ModuleCat.extendRestrictScalarsAdj (σ.comp ρ)).unit.app M m) =
      (ModuleCat.extendRestrictScalarsAdj σ).unit.app
        ((ModuleCat.extendScalars ρ).obj M)
          ((ModuleCat.extendRestrictScalarsAdj ρ).unit.app M m) :=
  ModuleCat.extendScalarsComp_hom_app_one_tmul ρ σ M m

/-- The inverse composition comparison combines the successive units. -/
theorem extendScalarsComp_inv_unit (ρ : R →+* R') (σ : R' →+* R'')
    (M : ModuleCat.{u} R) (m : M) :
    ((ModuleCat.extendScalarsComp ρ σ).app M).inv
        ((ModuleCat.extendRestrictScalarsAdj σ).unit.app
          ((ModuleCat.extendScalars ρ).obj M)
            ((ModuleCat.extendRestrictScalarsAdj ρ).unit.app M m)) =
      (ModuleCat.extendRestrictScalarsAdj (σ.comp ρ)).unit.app M m := by
  rw [← extendScalarsComp_unit, Iso.hom_inv_id_apply]

/-- Equality of coefficient maps transports their actual extension units. -/
theorem extendScalars_eqToIso_unit (ρ τ : R →+* R') (h : ρ = τ)
    (M : ModuleCat.{u} R) (m : M) :
    (eqToIso (congrArg (fun γ => (ModuleCat.extendScalars γ).obj M) h)).hom
        ((ModuleCat.extendRestrictScalarsAdj ρ).unit.app M m) =
      (ModuleCat.extendRestrictScalarsAdj τ).unit.app M m := by
  subst τ
  rfl

end ScalarUnits

variable {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S S' : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (f : S' ⟶ S)

/-- On sections, the actual eta stalk comparison is the inverse-image unit
followed by the coefficient-restriction comparison. -/
theorem etaStalkPullbackIso_germ (x : S') (U : S.Opens) (hx : f x ∈ U)
    (e : (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj.obj (.op U)) :
    (D.etaStalkPullbackIso f x).hom
        (TopCat.Presheaf.germ
          (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj U (f x) hx e) =
      TopCat.Presheaf.germ
        (latticeScalarSheaf d π (S' : TopCat) (D.pullback f).eta.lattice.sheaf).obj
          (f ⁻¹ᵁ U) x hx
            ((inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom.hom.app
              (.op (f ⁻¹ᵁ U))
                (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O)
                  f.base).unit.app
                    (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf)).hom.app
                      (.op U) e)) := by
  have h := congrArg
    (fun k => k ≫ (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
      (inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom.hom)
    (inverseImageStalkIso_germ f.base
      (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) x U hx)
  simp only [Category.assoc] at h
  rw [TopCat.Presheaf.stalkFunctor_map_germ] at h
  exact congrArg (fun k => k e) h

/-- The actual u map agrees under the eta comparison and structural stalk extension. -/
theorem uStalkPullback_square (x : S') (e : D.etaStalk (f x)) :
    (D.tangentStalkPullbackIso f x).hom
        ((D.pullback f).uStalkAdd x ((D.etaStalkPullbackIso f x).hom e)) =
      ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
        (ModuleCat.of (S.presheaf.stalk (f x)) (D.tangentStalk (f x))))
          (D.uStalkAdd (f x) e) := by
  obtain ⟨U, hx, e, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj e
  rw [D.etaStalkPullbackIso_germ, (D.pullback f).uStalkAdd_germ,
    D.uStalkAdd_germ]
  have h := congrArg (fun k => k.hom.app (.op U) e) (D.pullbackU_unit f)
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      D.tangent.graded.module).val.app (.op U) (D.u.hom.app (.op U) e) =
    (D.pullback f).u.hom.app (.op (f ⁻¹ᵁ U))
      ((inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf).hom.hom.app
        (.op (f ⁻¹ᵁ U))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base).unit.app
            (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf)).hom.app
              (.op U) e)) at h
  rw [← h]
  exact structuralPullbackStalkIso_unit_germ f x D.tangent.graded.module U hx _

/-- The forward tangent quotient comparison respects the actual quotient projections. -/
theorem tangentPiQuotientPullbackIso_hom_mkQ (x : S') (t : (D.pullback f).tangentStalk x) :
    (D.tangentPiQuotientPullbackIso f x).hom
        ((LinearMap.range ((D.pullback f).tangentStalkPi x)).mkQ t) =
      (ModuleCat.extendScalars (f.stalkMap x).hom).map
        (ModuleCat.ofHom (LinearMap.range (D.tangentStalkPi (f x))).mkQ)
          ((D.tangentStalkPullbackIso f x).hom t) := by
  have h := congrArg (fun k => (D.tangentStalkPullbackIso f x).hom ≫ k ≫
    (D.tangentPiQuotientPullbackIso f x).hom)
      (D.tangentPiQuotientPullbackIso_inv_mkQ f x)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] at h
  exact (congrArg (fun k => k t) h).symm

/-- The actual pulled u followed by the tangent quotient comparison, with the
original eta stalk as source. -/
def uPiQuotientPullbackMap (x : S') :
    D.etaStalk (f x) →+
      (ModuleCat.extendScalars (f.stalkMap x).hom).obj
        (ModuleCat.of (S.presheaf.stalk (f x)) (D.tangentPiQuotient (f x))) :=
  (D.tangentPiQuotientPullbackIso f x).hom.hom.toAddMonoidHom.comp
    ((LinearMap.range ((D.pullback f).tangentStalkPi x)).mkQ.toAddMonoidHom.comp
      (((D.pullback f).uStalkAdd x).comp
        (D.etaStalkPullbackIso f x).hom.hom.toAddMonoidHom))

/-- The quotient of u agrees with the actual local-ring extension unit. -/
theorem uPiQuotientPullback_square (x : S') (e : D.etaStalk (f x)) :
    (D.tangentPiQuotientPullbackIso f x).hom
        ((LinearMap.range ((D.pullback f).tangentStalkPi x)).mkQ
          ((D.pullback f).uStalkAdd x ((D.etaStalkPullbackIso f x).hom e))) =
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
        (ModuleCat.of (S.presheaf.stalk (f x)) (D.tangentPiQuotient (f x)))
          ((LinearMap.range (D.tangentStalkPi (f x))).mkQ (D.uStalkAdd (f x) e)) := by
  rw [D.tangentPiQuotientPullbackIso_hom_mkQ, D.uStalkPullback_square]
  exact extendScalars_unit_map (f.stalkMap x).hom
    (ModuleCat.ofHom (LinearMap.range (D.tangentStalkPi (f x))).mkQ) _

end SheafPreDatum

end Langlands.DeligneFormalSpace
