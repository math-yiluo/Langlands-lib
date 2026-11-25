/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath
public import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.StalkFrobenius

/-!
# The Weil fundamental representation of a lisse Weil sheaf

Let `C₀` be a curve over the finite field `K` with Weil group `W`, `C = C₀ ×_K K̄` the geometric
curve with geometric Galois Frobenius `Fr`, and fix base point data `B`
(`AlgebraicGeometry.WeilGroup.BasePointData`: a point `t` of `C`, a path `β : F_t ≅ F_{t ≫ Fr}`)
and a monodromy `M` of lisse sheaves on `C` (`AlgebraicGeometry.ProEtale.LisseMonodromy`).

Following `situation-weil`, a lisse Weil sheaf `ℱ` with Weil structure
`φ : Fr^* ℱ ≅ ℱ` gives:

* the geometric fundamental representation `ρ_geom` of `π₁(C, t) = Aut F_t` on the stalk
  `V = ℱ_t` (`AlgebraicGeometry.ProEtale.LisseMonodromy.rep`);
* the operator `T = Φ` on `V`, the composite of the transport `ℱ_t ≅ ℱ_{t ≫ Fr}` along `β`, the
  identification `ℱ_{t ≫ Fr} = (Fr^* ℱ)_t` and the stalk of `φ`
  (`AlgebraicGeometry.WeilGroup.frobStalkIso`), which satisfies
  `Φ ρ_geom(β ≫ Fr_* g ≫ β⁻¹) = ρ_geom(g) Φ` (`frobStalk_rep`);
* the Weil fundamental representation `ρ(u γⁿ) = ρ_geom(u) Φⁿ` of `W`, through an identification
  `π₁(C, t) ≅ W.geometric` under which the transport `g ↦ β ≫ Fr_* g ≫ β⁻¹` is conjugation by a
  degree-one element `γ` (`AlgebraicGeometry.WeilGroup.WeilMonodromyData`).

The identification and the degree-one element are provided by the homotopy exact sequence; here
they are hypotheses (`WeilMonodromyData`), so that this file only uses the sheaf theory.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

/-- The lisse Weil sheaves on `C`. -/
abbrev LisseWeilSheaf (K : Type u) [Field K] [Finite K] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar K ≠ l)] (C : Scheme.{u}) [C.Over (Spec (.of K))] :=
  ObjectProperty.FullSubcategory (fun F : WeilSheaf K l C ↦ F.IsLisse)

namespace WeilSheaf

/-- The underlying lisse `ℓ`-adic sheaf of a lisse Weil sheaf. -/
noncomputable abbrev toLisse (F : WeilSheaf K l C) (hF : F.IsLisse) :
    LisseSheaf l (C ↘ Spec (.of K)).geometricFiber :=
  ⟨F.obj.carrier, hF⟩

/-- The Weil structure as an isomorphism `Fr^* ℱ ≅ ℱ` of `ℓ`-adic sheaves, through
`Fr^* ≅ (Fr⁻¹)_*`. -/
noncomputable def adicFrobStr (F : WeilSheaf K l C) :
    ((C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].obj F.obj.carrier ≅
      F.obj.carrier :=
  (adicUpperStarIsoLowerStarInv l (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).app _ ≪≫
    F.obj.str

/-- The Weil structure as an isomorphism `Fr^* ℱ ≅ ℱ` of lisse sheaves. -/
noncomputable def lisseFrobStr (F : WeilSheaf K l C) (hF : F.IsLisse) :
    (F.toLisse hF).upperStar l (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom ≅
      F.toLisse hF :=
  (ObjectProperty.fullyFaithfulι _).preimageIso F.adicFrobStr

end WeilSheaf

namespace WeilGroup

variable [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
  (B : BasePointData W)

/-- The Frobenius `Φ : ℱ_t ≅ ℱ_t` of the Weil fundamental representation
(`situation-weil`): the transport `ℱ_t ≅ ℱ_{t ≫ Fr}` along the path `β`, the
identification `ℱ_{t ≫ Fr} = (Fr^* ℱ)_t`, and the stalk at `t` of the Weil structure
`Fr^* ℱ ≅ ℱ`. -/
noncomputable def frobStalkIso (F : WeilSheaf K l C) (hF : F.IsLisse) :
    (lisseStalk l B.t).obj (F.toLisse hF) ≅ (lisseStalk l B.t).obj (F.toLisse hF) :=
  (M.mono B.frobPath).app (F.toLisse hF) ≪≫
    upperStarStalkIso l (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t F.obj.carrier.X ≪≫
    (lisseStalk l B.t).mapIso (F.lisseFrobStr hF)

/-- The Frobenius `Φ` of the Weil fundamental representation, as a `ℚ̄_ℓ`-linear automorphism of
the stalk. -/
noncomputable def frobStalk (F : WeilSheaf K l C) (hF : F.IsLisse) :
    LisseMonodromy.StalkSpace B.t (F.toLisse hF) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (F.toLisse hF) :=
  WeilCoefficients.linearEquivOfIso (frobStalkIso M B F hF)

/-- Twisted equivariance of the Frobenius, as an identity of morphisms of stalks. -/
theorem mono_hom_app_comp_frobStalkIso_hom (F : WeilSheaf K l C) (hF : F.IsLisse)
    (g : Aut (fiber B.t)) :
    (M.mono (B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
        B.frobPath.symm)).hom.app (F.toLisse hF) ≫ (frobStalkIso M B F hF).hom =
      (frobStalkIso M B F hF).hom ≫ (M.mono g.asIso).hom.app (F.toLisse hF) := by
  have h₁ : (B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm) ≪≫ B.frobPath =
      B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso := by
    simp
  have e₁ := congrArg (fun τ ↦ (M.mono τ).hom.app (F.toLisse hF)) h₁
  rw [M.mono_trans (B.frobPath ≪≫ pullbackPathIso _ g.asIso ≪≫ B.frobPath.symm) B.frobPath,
    M.mono_trans B.frobPath (pullbackPathIso _ g.asIso)] at e₁
  simp only [Iso.trans_hom, NatTrans.comp_app] at e₁
  have e₂ := M.mono_upperStar (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso
    (F.toLisse hF)
  have e₃ := (M.mono g.asIso).hom.naturality (F.lisseFrobStr hF).hom
  simp only [frobStalkIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂, e₃]

/-- **Twisted equivariance of the Frobenius**: `Φ ρ_geom(β ≫ Fr_* g ≫ β⁻¹) = ρ_geom(g) Φ`. -/
theorem frobStalk_rep (F : WeilSheaf K l C) (hF : F.IsLisse) (g : Aut (fiber B.t))
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    frobStalk M B F hF (M.rep B.t (F.toLisse hF) (.of (B.frobPath ≪≫
        pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
          B.frobPath.symm)) v) =
      M.rep B.t (F.toLisse hF) g (frobStalk M B F hF v) := by
  have h := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
    (mono_hom_app_comp_frobStalkIso_hom M B F hF g)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The input from the homotopy exact sequence for the Weil fundamental representation: an
identification of `π₁(C, t) = Aut F_t` with the geometric part `W.geometric` of the Weil group, as
topological groups, and an element `γ` of degree one such that the transport
`g ↦ β ≫ Fr_* g ≫ β⁻¹` of loops at `t` along the Frobenius is conjugation by `γ`:
`g ↦ γ⁻¹ g γ`. -/
structure WeilMonodromyData where
  /-- The identification `π₁(C, t) ≅ W.geometric`. -/
  geomEquiv : Aut (fiber B.t) ≃ₜ* W.geometric
  /-- The lift of the Frobenius. -/
  frobLift : W.carrier
  deg_frobLift : W.deg frobLift = Multiplicative.ofAdd 1
  geomEquiv_conj (g : Aut (fiber B.t)) :
    (geomEquiv (.of (B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm)) : W.carrier) = frobLift⁻¹ * geomEquiv g * frobLift

variable {B} (D : WeilMonodromyData B)

/-- The degree datum `(W, deg, γ)` of the Weil group with the lift of the Frobenius. -/
noncomputable def WeilMonodromyData.degreeDatum : Monodromy.DegreeDatum W.carrier :=
  ⟨W.deg, W.deg_surjective, D.frobLift, D.deg_frobLift⟩

/-- The Frobenius `Φ` of the Weil fundamental representation, as a unit of the endomorphisms. -/
noncomputable def frobUnit (F : WeilSheaf K l C) (hF : F.IsLisse) :
    (Module.End (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF)))ˣ where
  val := (frobStalk M B F hF).toLinearMap
  inv := (frobStalk M B F hF).symm.toLinearMap
  val_inv := LinearMap.ext fun v ↦ (frobStalk M B F hF).apply_symm_apply v
  inv_val := LinearMap.ext fun v ↦ (frobStalk M B F hF).symm_apply_apply v

/-- The geometric fundamental representation `ρ_geom`, on `W.geometric ≅ π₁(C, t)`. -/
noncomputable def geomUnits (F : WeilSheaf K l C) (hF : F.IsLisse) :
    W.geometric →* (Module.End (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (F.toLisse hF)))ˣ :=
  (M.rep B.t (F.toLisse hF)).asGroupHom.comp D.geomEquiv.symm.toMonoidHom

/-- The Frobenius conjugates the geometric fundamental representation as `γ` conjugates
`W.geometric`: `Φ ρ_geom(u) Φ⁻¹ = ρ_geom(γ u γ⁻¹)`. -/
theorem frobUnit_conj (F : WeilSheaf K l C) (hF : F.IsLisse) (u : W.carrier)
    (hu : u ∈ D.degreeDatum.deg.ker) :
    frobUnit M F hF * geomUnits M D F hF ⟨u, hu⟩ * (frobUnit M F hF)⁻¹ =
      geomUnits M D F hF ⟨D.degreeDatum.degreeOneElement * u * D.degreeDatum.degreeOneElement⁻¹,
        D.degreeDatum.deg.normal_ker.conj_mem u hu _⟩ := by
  set g := D.geomEquiv.symm ⟨D.frobLift * u * D.frobLift⁻¹,
    D.degreeDatum.deg.normal_ker.conj_mem u hu _⟩
  have hk : D.geomEquiv.symm ⟨u, hu⟩ = .of (B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm) := by
    apply D.geomEquiv.injective
    apply Subtype.ext
    rw [ContinuousMulEquiv.apply_symm_apply, D.geomEquiv_conj, ContinuousMulEquiv.apply_symm_apply]
    simp only
    group
  refine Units.ext (LinearMap.ext fun w ↦ ?_)
  obtain ⟨v, rfl⟩ := (frobStalk M B F hF).surjective w
  change frobStalk M B F hF (M.rep B.t (F.toLisse hF) (D.geomEquiv.symm ⟨u, hu⟩)
      ((frobStalk M B F hF).symm (frobStalk M B F hF v))) =
    M.rep B.t (F.toLisse hF) g (frobStalk M B F hF v)
  rw [LinearEquiv.symm_apply_apply, hk, frobStalk_rep]

/-- **The Weil fundamental representation** of a lisse Weil sheaf (blueprint:
`situation-weil`): the representation `ρ(u γⁿ) = ρ_geom(u) Φⁿ` of the Weil
group on the stalk `ℱ_t`, extending the geometric fundamental representation by the Frobenius
`Φ` of the Weil structure (`AlgebraicGeometry.Monodromy.DegreeDatum.lift`,
`situation-weil`). -/
noncomputable def fundamentalRep (F : WeilSheaf K l C) (hF : F.IsLisse) :
    Representation (PadicAlgCl l) W.carrier (LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :=
  (Units.coeHom _).comp
    (D.degreeDatum.lift (geomUnits M D F hF) (frobUnit M F hF) (frobUnit_conj M D F hF))

/-- On the geometric part, the Weil fundamental representation is the geometric fundamental
representation. -/
theorem fundamentalRep_geometric (F : WeilSheaf K l C) (hF : F.IsLisse) (u : W.geometric) :
    fundamentalRep M D F hF u = M.rep B.t (F.toLisse hF) (D.geomEquiv.symm u) := by
  simp only [fundamentalRep, MonoidHom.comp_apply, Units.coeHom_apply]
  rw [Monodromy.DegreeDatum.lift_apply_of_mem_ker _ _ _ _ u.2]
  rfl

/-- The Weil fundamental representation sends the lift of the Frobenius to `Φ`. -/
theorem fundamentalRep_frobLift (F : WeilSheaf K l C) (hF : F.IsLisse) :
    fundamentalRep M D F hF D.frobLift = (frobStalk M B F hF).toLinearMap := by
  simp only [fundamentalRep, MonoidHom.comp_apply, Units.coeHom_apply]
  exact congrArg Units.val (Monodromy.DegreeDatum.lift_degreeOneElement (D := D.degreeDatum) _ _ _)

end WeilGroup

namespace WeilSheaf

/-- The morphism of underlying lisse sheaves of a morphism of lisse Weil sheaves. -/
noncomputable abbrev toLisseMap {F G : WeilSheaf K l C} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) : F.toLisse hF ⟶ G.toLisse hG :=
  ObjectProperty.homMk ((Endofunctor.IsoAlgebra.forget _).map φ.hom)

/-- A morphism of Weil sheaves commutes with the Weil structures `Fr^* ℱ ≅ ℱ`. -/
theorem adicFrobStr_naturality {F G : WeilSheaf K l C} (φ : F ⟶ G) :
    ((C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
        ((Endofunctor.IsoAlgebra.forget _).map φ.hom) ≫ G.adicFrobStr.hom =
      F.adicFrobStr.hom ≫ (Endofunctor.IsoAlgebra.forget _).map φ.hom := by
  have h := φ.hom.hom.h
  simp only [adicFrobStr, Iso.trans_hom, Iso.app_hom, Category.assoc,
    Endofunctor.IsoAlgebra.forget_map, Endofunctor.IsoAlgebra.str_hom]
  rw [← h]
  exact (adicUpperStarIsoLowerStarInv l _).hom.naturality_assoc _ _

end WeilSheaf

namespace WeilGroup

variable [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
  {B : BasePointData W}

/-- The Frobenius of the stalks is natural in the lisse Weil sheaf. -/
theorem frobStalkIso_naturality {F G : WeilSheaf K l C} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) ≫ (frobStalkIso M B G hG).hom =
      (frobStalkIso M B F hF).hom ≫ (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) := by
  have e₁ : (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) ≫
      (M.mono B.frobPath).hom.app (G.toLisse hG) =
      (M.mono B.frobPath).hom.app (F.toLisse hF) ≫
        (lisseStalk l _).map (WeilSheaf.toLisseMap φ hF hG) :=
    (M.mono B.frobPath).hom.naturality (WeilSheaf.toLisseMap φ hF hG)
  have e₃ := (lisseStalk l B.t).congr_map (ObjectProperty.hom_ext _
    (WeilSheaf.adicFrobStr_naturality φ) :
      (ObjectProperty.homMk (((C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
        ((Endofunctor.IsoAlgebra.forget _).map φ.hom)) :
          (F.toLisse hF).upperStar l _ ⟶ (G.toLisse hG).upperStar l _) ≫
        (G.lisseFrobStr hG).hom =
      (F.lisseFrobStr hF).hom ≫ WeilSheaf.toLisseMap φ hF hG)
  rw [Functor.map_comp, Functor.map_comp] at e₃
  have e₁' : ∀ {Z} (h : _ ⟶ Z), (lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG) ≫
      (M.mono B.frobPath).hom.app (G.toLisse hG) ≫ h = (M.mono B.frobPath).hom.app (F.toLisse hF) ≫
        (lisseStalk l _).map (WeilSheaf.toLisseMap φ hF hG) ≫ h := fun h ↦ by
    rw [← Category.assoc, e₁, Category.assoc]
  simp only [frobStalkIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [e₁']
  congr 1
  have key := upperStarStalkIso_hom_naturality l
    (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t
    ((Endofunctor.IsoAlgebra.forget _).map φ.hom).hom
  erw [reassoc_of% key]
  congr 1

/-- The map `ℱ_t → 𝒢_t` of stalks induced by a morphism of lisse Weil sheaves. -/
noncomputable def stalkMap {F G : WeilSheaf K l C} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    LisseMonodromy.StalkSpace B.t (F.toLisse hF) →ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (G.toLisse hG) :=
  ((WeilCoefficients.toModuleCat l).map
    ((lisseStalk l B.t).map (WeilSheaf.toLisseMap φ hF hG))).hom

/-- Stalk maps commute with the Frobenius `Φ`. -/
theorem stalkMap_frobStalk {F G : WeilSheaf K l C} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    stalkMap (B := B) φ hF hG (frobStalk M B F hF v) =
      frobStalk M B G hG (stalkMap (B := B) φ hF hG v) := by
  have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    (frobStalkIso_naturality M (B := B) φ hF hG)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- Stalk maps commute with the geometric fundamental representation. -/
theorem stalkMap_rep {F G : WeilSheaf K l C} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) (g : Aut (fiber B.t)) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    stalkMap (B := B) φ hF hG (M.rep B.t (F.toLisse hF) g v) =
      M.rep B.t (G.toLisse hG) g (stalkMap (B := B) φ hF hG v) := by
  have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    ((M.mono g.asIso).hom.naturality (WeilSheaf.toLisseMap φ hF hG))
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

variable {M} (D : WeilMonodromyData B)

omit [Fact (ringChar K ≠ l)] in
/-- A linear map between two representations of the Weil group which intertwines them on the
geometric part and at the lift of the Frobenius intertwines them everywhere: `W` is generated by
`W.geometric` and the lift of the Frobenius. -/
theorem intertwines_of_geometric_frobLift {V V' : Type*} [AddCommGroup V]
    [Module (PadicAlgCl l) V] [AddCommGroup V'] [Module (PadicAlgCl l) V']
    (ρ : Representation (PadicAlgCl l) W.carrier V)
    (ρ' : Representation (PadicAlgCl l) W.carrier V')
    (S : V →ₗ[PadicAlgCl l] V') (hgeom : ∀ u ∈ W.geometric, ∀ v, S (ρ u v) = ρ' u (S v))
    (hfrob : ∀ v, S (ρ D.frobLift v) = ρ' D.frobLift (S v)) (w : W.carrier) (v : V) :
    S (ρ w v) = ρ' w (S v) := by
  let H : Subgroup W.carrier :=
    { carrier := {w | ∀ v, S (ρ w v) = ρ' w (S v)}
      mul_mem' := fun {a b} ha hb v ↦ by
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
        rw [ha, hb]
      one_mem' := fun v ↦ by simp
      inv_mem' := fun {a} ha v ↦ by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have h := ha (ρ a⁻¹ v)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h
        rw [h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] }
  have hw : w = (w * (D.degreeDatum.degreeOneElement ^ (D.degreeDatum.deg w).toAdd)⁻¹) *
      D.degreeDatum.degreeOneElement ^ (D.degreeDatum.deg w).toAdd := by group
  have : w ∈ H := by
    rw [hw]
    refine H.mul_mem (hgeom _ (D.degreeDatum.mul_inv_zpow_mem_ker w)) (H.zpow_mem ?_ _)
    exact hfrob
  exact this v

/-- Stalk maps intertwine the Weil fundamental representations. -/
theorem stalkMap_fundamentalRep {F G : WeilSheaf K l C} (φ : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) (w : W.carrier) (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    stalkMap (B := B) φ hF hG (fundamentalRep M D F hF w v) =
      fundamentalRep M D G hG w (stalkMap (B := B) φ hF hG v) := by
  refine intertwines_of_geometric_frobLift D _ _ _ (fun u hu v ↦ ?_) (fun v ↦ ?_) w v
  · rw [fundamentalRep_geometric M D F hF ⟨u, hu⟩, fundamentalRep_geometric M D G hG ⟨u, hu⟩]
    exact stalkMap_rep M φ hF hG _ v
  · rw [fundamentalRep_frobLift, fundamentalRep_frobLift]
    exact stalkMap_frobStalk M φ hF hG v

/-- The Weil fundamental representation is continuous on the geometric part, as soon as the
geometric fundamental representation is continuous. -/
theorem fundamentalRep_isContinuousOn (F : WeilSheaf K l C) (hF : F.IsLisse)
    (hM : M.IsEquivalenceAt B.t) :
    (fundamentalRep M D F hF).IsContinuousOn W.geometric.subtype := by
  intro ψ v
  have : (fun u : W.geometric ↦ ψ (fundamentalRep M D F hF (W.geometric.subtype u) v)) =
      (fun g ↦ ψ (M.rep B.t (F.toLisse hF) g v)) ∘ D.geomEquiv.symm := by
    funext u
    simp only [Function.comp_apply, Subgroup.subtype_apply]
    rw [fundamentalRep_geometric]
  rw [this]
  exact (hM.continuous_rep _ ψ v).comp D.geomEquiv.symm.continuous

variable (M) in
/-- The transport of stalks of a lisse sheaf `𝒢` from `t` to `t ≫ Fr` along `β`, followed by the
identification `𝒢_{t ≫ Fr} = (Fr^* 𝒢)_t`. -/
noncomputable def frobPathStalkIso (G : LisseSheaf l (C ↘ Spec (.of K)).geometricFiber) :
    (lisseStalk l B.t).obj G ≅
      (lisseStalk l B.t).obj (G.upperStar l
        (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) :=
  (M.mono B.frobPath).app G ≪≫
    upperStarStalkIso l (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t G.obj.X

omit [Fact (ringChar K ≠ l)] in
variable (M) in
/-- `frobPathStalkIso` is natural in the lisse sheaf. -/
theorem frobPathStalkIso_naturality {G H : LisseSheaf l (C ↘ Spec (.of K)).geometricFiber}
    (f : G ⟶ H) :
    (lisseStalk l B.t).map f ≫ (frobPathStalkIso M (B := B) H).hom =
      (frobPathStalkIso M G).hom ≫ (lisseStalk l B.t).map
        (ObjectProperty.homMk (((C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map
          f.hom) : G.upperStar l _ ⟶ H.upperStar l _) := by
  have e₁ : (lisseStalk l B.t).map f ≫ (M.mono B.frobPath).hom.app H =
      (M.mono B.frobPath).hom.app G ≫ (lisseStalk l _).map f :=
    (M.mono B.frobPath).hom.naturality f
  have key := upperStarStalkIso_hom_naturality l
    (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom B.t f.hom.hom
  simp only [frobPathStalkIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, e₁, Category.assoc]
  exact congrArg ((M.mono B.frobPath).hom.app G ≫ ·) key

omit [Fact (ringChar K ≠ l)] in
variable (M) in
/-- Conjugating the transport `β ≫ Fr_* g ≫ β⁻¹` by `frobPathStalkIso` gives the monodromy of
`g` on `Fr^* 𝒢`. -/
theorem frobPathStalkIso_conj (G : LisseSheaf l (C ↘ Spec (.of K)).geometricFiber)
    (g : Aut (fiber B.t)) :
    (M.mono (B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
        B.frobPath.symm)).hom.app G ≫ (frobPathStalkIso M G).hom =
      (frobPathStalkIso M G).hom ≫ (M.mono g.asIso).hom.app
        (G.upperStar l
        (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) := by
  have h₁ : (B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
      B.frobPath.symm) ≪≫ B.frobPath =
      B.frobPath ≪≫
      pullbackPathIso (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso := by
    simp
  have e₁ := congrArg (fun τ ↦ (M.mono τ).hom.app G) h₁
  rw [M.mono_trans (B.frobPath ≪≫ pullbackPathIso _ g.asIso ≪≫ B.frobPath.symm) B.frobPath,
    M.mono_trans B.frobPath (pullbackPathIso _ g.asIso)] at e₁
  simp only [Iso.trans_hom, NatTrans.comp_app] at e₁
  have e₂ := M.mono_upperStar (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso G
  simp only [frobPathStalkIso, Iso.trans_hom, Iso.app_hom]
  rw [reassoc_of% e₁, e₂]
  simp only [Category.assoc]

omit [Fact (ringChar K ≠ l)] in
/-- A morphism of `WeilCoefficients` is determined by its underlying `ℚ̄_ℓ`-linear map. -/
lemma _root_.AlgebraicGeometry.WeilCoefficients.hom_ext_toModuleCat {A A' : WeilCoefficients.{u} l}
    {a b : A ⟶ A'}
    (h : ((WeilCoefficients.toModuleCat l).map a).hom =
      ((WeilCoefficients.toModuleCat l).map b).hom) :
    a = b :=
  ModuleCat.hom_ext (LinearMap.ext fun x ↦ LinearMap.congr_fun h x)

omit [IsCurve (C ↘ Spec (.of K))] in
/-- Morphisms of lisse Weil sheaves are determined by the underlying morphisms of sheaves. -/
lemma _root_.AlgebraicGeometry.LisseWeilSheaf.hom_ext {X Y : LisseWeilSheaf K l C} {f f' : X ⟶ Y}
    (h : WeilSheaf.toLisseMap f.hom X.property Y.property =
      WeilSheaf.toLisseMap f'.hom X.property Y.property) : f = f' := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Endofunctor.IsoAlgebra.hom_ext
  exact congrArg (fun φ ↦ φ.hom) h

variable (M) in
/-- The stalk functor at `t` on lisse Weil sheaves is faithful. -/
theorem stalkMap_injective (hM : M.IsEquivalenceAt B.t) {X Y : LisseWeilSheaf K l C}
    (f f' : X ⟶ Y)
    (h : stalkMap (B := B) f.hom X.property Y.property = stalkMap f'.hom X.property Y.property) :
    f = f' :=
  LisseWeilSheaf.hom_ext (hM.faithful _ _ (WeilCoefficients.hom_ext_toModuleCat h))

/-- The Frobenius `Φ` is the stalk of the Weil structure after `frobPathStalkIso`. -/
lemma frobStalk_apply (F : WeilSheaf K l C) (hF : F.IsLisse)
    (v : LisseMonodromy.StalkSpace B.t (F.toLisse hF)) :
    frobStalk M B F hF v = ((WeilCoefficients.toModuleCat l).map
      ((lisseStalk l B.t).map (F.lisseFrobStr hF).hom)).hom
        (((WeilCoefficients.toModuleCat l).map (frobPathStalkIso M (F.toLisse hF)).hom).hom v) :=
  rfl

/-- A morphism of lisse sheaves between lisse Weil sheaves whose stalk at `t` commutes with the
Frobenius `Φ` commutes with the Weil structures. -/
theorem upperStar_comp_lisseFrobStr_of_frobStalk (hM : M.IsEquivalenceAt B.t)
    {F G : WeilSheaf K l C} (hF : F.IsLisse) (hG : G.IsLisse) (f : F.toLisse hF ⟶ G.toLisse hG)
    (hf : ∀ v, ((WeilCoefficients.toModuleCat l).map ((lisseStalk l B.t).map f)).hom
        (frobStalk M B F hF v) =
      frobStalk M B G hG
        (((WeilCoefficients.toModuleCat l).map ((lisseStalk l B.t).map f)).hom v)) :
    (ObjectProperty.homMk
      (((C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom)^*ᵃ[l].map f.hom) :
        (F.toLisse hF).upperStar l _ ⟶ (G.toLisse hG).upperStar l _) ≫ (G.lisseFrobStr hG).hom =
      (F.lisseFrobStr hF).hom ≫ f := by
  apply hM.faithful
  apply WeilCoefficients.hom_ext_toModuleCat
  refine LinearMap.ext fun w ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v, ((WeilCoefficients.toModuleCat l).map
      (frobPathStalkIso M (B := B) (F.toLisse hF)).hom).hom v = w :=
    (WeilCoefficients.linearEquivOfIso (frobPathStalkIso M (B := B) (F.toLisse hF))).surjective w
  have n := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
    (frobPathStalkIso_naturality M (B := B) f)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at n ⊢
  rw [← n]
  exact (hf v).symm

/-- **Fullness of the Weil fundamental representation**: a linear map of stalks intertwining the
Weil fundamental representations is the stalk of a morphism of lisse Weil sheaves. On the
geometric part it is the stalk of a morphism of lisse sheaves, by
`proposition-lattices-representations-normal-scheme`; commuting with `Φ`, this morphism commutes
with the Weil structures. -/
theorem exists_stalkMap_eq (hM : M.IsEquivalenceAt B.t) {X Y : LisseWeilSheaf K l C}
    (φ : LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property) →ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t (Y.obj.toLisse Y.property))
    (hφ : ∀ w v, φ (fundamentalRep M D X.obj X.property w v) =
      fundamentalRep M D Y.obj Y.property w (φ v)) :
    ∃ f : X ⟶ Y, stalkMap (B := B) f.hom X.property Y.property = φ := by
  obtain ⟨f₀, hf₀⟩ := hM.full φ fun g v ↦ by
    have h := hφ (D.geomEquiv g) v
    rwa [fundamentalRep_geometric, fundamentalRep_geometric,
      ContinuousMulEquiv.symm_apply_apply] at h
  have key := upperStar_comp_lisseFrobStr_of_frobStalk hM X.property Y.property f₀ fun v ↦ by
    rw [hf₀]
    have h := hφ D.frobLift v
    rwa [fundamentalRep_frobLift, fundamentalRep_frobLift] at h
  have key' := congrArg (fun ψ ↦ ψ.hom) key
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    WeilSheaf.lisseFrobStr, Functor.FullyFaithful.preimageIso_hom, ObjectProperty.ι_obj,
    WeilSheaf.adicFrobStr, Iso.trans_hom, Iso.app_hom, Category.assoc] at key'
  have hstr : (WeilSheaf.frobeniusPullback K l C).map f₀.hom ≫ Y.obj.obj.obj.str =
      X.obj.obj.obj.str ≫ f₀.hom := by
    rw [← cancel_epi ((adicUpperStarIsoLowerStarInv l
      (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).hom.app X.obj.obj.carrier),
      ← (adicUpperStarIsoLowerStarInv l _).hom.naturality_assoc]
    exact key'
  exact ⟨ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk ⟨f₀.hom, hstr⟩)), hf₀⟩

/-- **Essential surjectivity of the Weil fundamental representation**: every finite-dimensional
representation of the Weil group which is continuous on the geometric part is the Weil fundamental
representation of a lisse Weil sheaf. Its restriction to the geometric part is the monodromy of a
lisse sheaf `𝒢` (`proposition-lattices-representations-normal-scheme`), and the action of the lift
`γ` of the Frobenius defines the Weil structure `Fr^* 𝒢 ≅ 𝒢` through `frobPathStalkIso`
(`definition-weil-representation--1`, Frobenius descent). -/
theorem exists_fundamentalRep_linearEquiv (hM : M.IsEquivalenceAt B.t) (V : Type (u + 1))
    [AddCommGroup V] [Module (PadicAlgCl l) V] [FiniteDimensional (PadicAlgCl l) V]
    (ρ : Representation (PadicAlgCl l) W.carrier V) (hρ : ρ.IsContinuousOn W.geometric.subtype) :
    ∃ (X : LisseWeilSheaf K l C)
      (e : LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property) ≃ₗ[PadicAlgCl l] V),
      ∀ w v, e (fundamentalRep M D X.obj X.property w v) = ρ w (e v) := by
  let ρg : Representation (PadicAlgCl l) (Aut (fiber B.t)) V :=
    ρ.comp (W.geometric.subtype.comp D.geomEquiv.toMonoidHom)
  obtain ⟨G₀, e, he⟩ := hM.essSurj V ρg fun φ v ↦ (hρ φ v).comp D.geomEquiv.continuous
  have he' (g : Aut (fiber B.t)) (x : V) : e.symm (ρg g x) = M.rep B.t G₀ g (e.symm x) := by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  let P := WeilCoefficients.linearEquivOfIso (frobPathStalkIso M (B := B) G₀)
  have hP (g : Aut (fiber B.t)) (v : LisseMonodromy.StalkSpace B.t G₀) :
      P (M.rep B.t G₀ (.of (B.frobPath ≪≫ pullbackPathIso
        (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom g.asIso ≪≫
          B.frobPath.symm)) v) =
      M.rep B.t _ g (P v) := by
    have h := congrArg (fun ψ ↦ ((WeilCoefficients.toModuleCat l).map ψ).hom v)
      (frobPathStalkIso_conj M (B := B) G₀ g)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  let Rγ := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom D.frobLift)
  have hRγ (x : V) : Rγ x = ρ D.frobLift x := rfl
  let φ : LisseMonodromy.StalkSpace B.t
      (G₀.upperStar l (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso.hom) ≃ₗ[PadicAlgCl l]
      LisseMonodromy.StalkSpace B.t G₀ :=
    P.symm ≪≫ₗ e ≪≫ₗ Rγ ≪≫ₗ e.symm
  have hφP (w : LisseMonodromy.StalkSpace B.t G₀) : φ (P w) = e.symm (ρ D.frobLift (e w)) := by
    simp only [φ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hRγ]
  have hφ (g : Aut (fiber B.t)) (v) : φ (M.rep B.t _ g v) = M.rep B.t G₀ g (φ v) := by
    obtain ⟨w, rfl⟩ := P.surjective v
    have hc := D.geomEquiv_conj g
    rw [← hP, hφP, hφP, he, ← he']
    congr 1
    change ρ D.frobLift (ρ (D.geomEquiv _ : W.carrier) (e w)) =
      ρ (D.geomEquiv g : W.carrier) (ρ D.frobLift (e w))
    rw [hc, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  obtain ⟨ψ, hψ⟩ := hM.full φ.toLinearMap hφ
  have : IsIso ψ := hM.isIso_of_bijective ψ (by rw [hψ]; exact φ.bijective)
  let str : (WeilSheaf.frobeniusPullback K l C).obj G₀.obj ≅ G₀.obj :=
    ((adicUpperStarIsoLowerStarInv l (C ↘ Spec (.of K)).geometricGaloisFrobenius.asIso).app
      G₀.obj).symm ≪≫ (ObjectProperty.ι _).mapIso (asIso ψ)
  let F : WeilSheaf K l C :=
    ⟨Endofunctor.IsoAlgebra.mk G₀.obj str, G₀.property.isAdicConstructibleSheaf⟩
  have hF : F.IsLisse := G₀.property
  have hfrob (v : LisseMonodromy.StalkSpace B.t G₀) :
      frobStalk M B F hF v = e.symm (ρ D.frobLift (e v)) := by
    have hψF : (F.lisseFrobStr hF).hom = ψ := by
      apply ObjectProperty.hom_ext
      simp [F, str, WeilSheaf.lisseFrobStr, WeilSheaf.adicFrobStr, Endofunctor.IsoAlgebra.str,
        Endofunctor.IsoAlgebra.mk]
    rw [frobStalk_apply, ← hφP, hψF]
    exact LinearMap.congr_fun hψ (P v)
  refine ⟨⟨F, hF⟩, e, fun w v ↦ ?_⟩
  refine intertwines_of_geometric_frobLift D _ _ e.toLinearMap (fun u hu v ↦ ?_) (fun v ↦ ?_) w v
  · change e (fundamentalRep M D F hF u v) = ρ u (e v)
    rw [fundamentalRep_geometric M D F hF ⟨u, hu⟩]
    refine (he _ v).trans ?_
    simp only [ρg, MonoidHom.comp_apply, Subgroup.subtype_apply]
    erw [ContinuousMulEquiv.apply_symm_apply]
  · change e (fundamentalRep M D F hF D.frobLift v) = ρ D.frobLift (e v)
    rw [fundamentalRep_frobLift]
    change e (frobStalk M B F hF v) = _
    rw [hfrob, LinearEquiv.apply_symm_apply]

/-- The stalks of lisse Weil sheaves are finite-dimensional. -/
instance (X : LisseWeilSheaf K l C) :
    FiniteDimensional (PadicAlgCl l) (LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property)) :=
  X.obj.finiteDimensional_stalkObj B.t

variable (M) in
/-- **The lisse sheaf–representation equivalence** at the level of the Weil fundamental
representation (blueprint: `definition-weil-representation--1`): if the monodromy
at `t` is an equivalence (`proposition-lattices-representations-normal-scheme`), the Weil
fundamental representation is an equivalence between lisse Weil sheaves and lisse representations of
the Weil group, under which every lisse Weil sheaf goes to a representation isomorphic to its Weil
fundamental representation. -/
theorem exists_equivalence_fundamentalRep (hM : M.IsEquivalenceAt B.t) :
    ∃ e : LisseWeilSheaf K l C ≌ (W.isLisseRep l).FullSubcategory,
      ∀ X : LisseWeilSheaf K l C, ∃ f : (e.functor.obj X).obj.V ≃ₗ[PadicAlgCl l]
          LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property),
        ∀ g v, f ((e.functor.obj X).obj.ρ g v) = fundamentalRep M D X.obj X.property g (f v) := by
  refine Representation.exists_equivalence_of_realization W.geometric.subtype
    (fun X : LisseWeilSheaf K l C ↦ LisseMonodromy.StalkSpace B.t (X.obj.toLisse X.property))
    (fun X ↦ fundamentalRep M D X.obj X.property)
    (fun X ↦ fundamentalRep_isContinuousOn D X.obj X.property hM)
    (fun {X Y : LisseWeilSheaf K l C} (f : X ⟶ Y) ↦ stalkMap f.hom X.property Y.property)
    (fun X ↦ ?_) (fun f g ↦ ?_)
    (fun {X Y : LisseWeilSheaf K l C} (f : X ⟶ Y) w v ↦ stalkMap_fundamentalRep D f.hom _ _ w v)
    (fun f f' h ↦ stalkMap_injective M hM f f' h)
    (fun φ hφ ↦ exists_stalkMap_eq D hM φ hφ)
    (fun V _ _ _ ρ hρ ↦ exists_fundamentalRep_linearEquiv D hM V ρ hρ) _ fun X ↦ ?_
  · simp only [stalkMap]
    rw [show WeilSheaf.toLisseMap (𝟙 X : X ⟶ X).hom X.property X.property = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  · simp only [stalkMap]
    rw [show WeilSheaf.toLisseMap (f ≫ g).hom _ _ =
      WeilSheaf.toLisseMap f.hom _ _ ≫ WeilSheaf.toLisseMap g.hom _ _ from rfl,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl
  · refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun φ v ↦ h₂.continuous_apply φ v⟩,
      fun ⟨h₁, h₂⟩ ↦ ⟨h₁, WeilGroup.IsLisse.of_continuous_apply fun φ v ↦ h₂ φ v⟩⟩

end WeilGroup

end AlgebraicGeometry
