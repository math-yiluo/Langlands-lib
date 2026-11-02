import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.Torus.Split

/-! # Diagonalizable group schemes of character groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Diagonalizable

variable (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ]

/-! ### The character functor and its corepresentation -/

/-- The functor `B ↦ Hom(Λ, Bˣ)` on commutative `R`-algebras. -/
def commFunctor : CommAlgCat.{u} R ⥤ CommGrpCat.{u} where
  obj B := CommGrpCat.of (Multiplicative Λ →* Bˣ)
  map f := CommGrpCat.ofHom (MonoidHom.compHom (Units.map f.hom.toRingHom.toMonoidHom))
  map_id B := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    apply MonoidHom.ext
    intro m
    apply Units.ext
    rfl
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    apply MonoidHom.ext
    intro m
    apply Units.ext
    rfl

/-- The group-valued character functor. -/
abbrev functor : CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  commFunctor R Λ ⋙ forget₂ CommGrpCat GrpCat

@[simp] theorem commFunctor_map_apply {B C : CommAlgCat.{u} R} (f : B ⟶ C)
    (χ : Multiplicative Λ →* Bˣ) (m : Multiplicative Λ) :
    (DFunLike.coe (F := Multiplicative Λ →* Cˣ) ((commFunctor R Λ).map f χ) m : C) =
      f.hom (χ m : B) :=
  rfl

/-- The group algebra `R[Λ]`. -/
abbrev algebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (AddMonoidAlgebra R Λ)

/-- The monomials `single γ 1` as units of the group algebra. -/
abbrev monomialUnits : Multiplicative Λ →* (AddMonoidAlgebra R Λ)ˣ :=
  (AddMonoidAlgebra.of R Λ).toHomUnits

@[simp] theorem monomialUnits_val (m : Multiplicative Λ) :
    (monomialUnits R Λ m : AddMonoidAlgebra R Λ) = AddMonoidAlgebra.single m.toAdd 1 :=
  rfl

/-- The algebra map from the group algebra evaluating a character on the monomials. -/
abbrev lift {B : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Bˣ) : algebra R Λ ⟶ B :=
  CommAlgCat.ofHom (AddMonoidAlgebra.lift R B Λ ((Units.coeHom B).comp χ))

@[simp] theorem lift_single {B : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Bˣ) (γ : Λ)
    (r : R) : (lift R Λ χ).hom (AddMonoidAlgebra.single γ r) = r • (χ (.ofAdd γ) : B) := by
  simp [lift]

/-- The group algebra corepresents the character functor. -/
def corepresentation :
    (commFunctor R Λ ⋙ forget CommGrpCat).CorepresentableBy (algebra R Λ) where
  homEquiv :=
    { toFun := fun f => (Units.map f.hom.toRingHom.toMonoidHom).comp (monomialUnits R Λ)
      invFun := fun χ => lift R Λ χ
      left_inv := fun f => by
        apply CommAlgCat.hom_ext
        apply AddMonoidAlgebra.algHom_ext
        · intro γ
          simp
        · exact Subsingleton.elim _ _
      right_inv := fun χ => by
        apply MonoidHom.ext
        intro m
        apply Units.ext
        simp
        rfl }
  homEquiv_comp g f := by
    apply MonoidHom.ext
    intro m
    apply Units.ext
    rfl

theorem corepresentation_homEquiv_apply {B : CommAlgCat.{u} R} (f : algebra R Λ ⟶ B)
    (m : Multiplicative Λ) :
    (DFunLike.coe (F := Multiplicative Λ →* Bˣ) ((corepresentation R Λ).homEquiv f) m : B) =
      f.hom (AddMonoidAlgebra.single m.toAdd 1) :=
  rfl

theorem corepresentation_homEquiv_symm {B : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Bˣ) :
    (corepresentation R Λ).homEquiv.symm χ = lift R Λ χ :=
  rfl

/-- The diagonalizable group scheme `D(Λ)` over `Spec R`: the spectrum of the group algebra
`R[Λ]`, with points `Hom(Λ, Γ(T, 𝒪_T)ˣ)` over every test scheme `T`. -/
abbrev groupScheme : CommGroupScheme (Spec R) :=
  Corepresented.commGroupScheme (commFunctor R Λ) (corepresentation R Λ)

theorem groupScheme_toGrp :
    (groupScheme R Λ).toGrp = Corepresented.groupScheme (functor R Λ) (corepresentation R Λ) :=
  rfl

/-- The corepresentation, viewed for the group-valued character functor. -/
abbrev grpCorepresentation :
    (functor R Λ ⋙ forget GrpCat).CorepresentableBy (algebra R Λ) :=
  corepresentation R Λ

/-! ### Comultiplication and antipode on monomials -/

theorem comul_single (γ : Λ) (r : R) :
    (Corepresented.LinearEmbedding.comul (grpCorepresentation R Λ)).hom (AddMonoidAlgebra.single γ r) =
      AddMonoidAlgebra.single γ r ⊗ₜ[R] AddMonoidAlgebra.single γ 1 := by
  change (lift R Λ _).hom (AddMonoidAlgebra.single γ r) = _
  erw [lift_single]
  change r • ((AddMonoidAlgebra.single γ 1 ⊗ₜ[R] (1 : AddMonoidAlgebra R Λ)) *
    ((1 : AddMonoidAlgebra R Λ) ⊗ₜ[R] AddMonoidAlgebra.single γ 1)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul',
    AddMonoidAlgebra.smul_single', mul_one]

theorem antipode_single (γ : Λ) (r : R) :
    (Corepresented.antipode (grpCorepresentation R Λ)).hom (AddMonoidAlgebra.single γ r) =
      AddMonoidAlgebra.single (-γ) r := by
  change (lift R Λ _).hom (AddMonoidAlgebra.single γ r) = _
  erw [lift_single]
  change r • (((monomialUnits R Λ (.ofAdd γ))⁻¹ : (AddMonoidAlgebra R Λ)ˣ) :
    AddMonoidAlgebra R Λ) = _
  rw [← map_inv, monomialUnits_val, AddMonoidAlgebra.smul_single', mul_one]
  rfl

/-! ### Restriction along homomorphisms of character groups -/

section Restrict

variable {Λ} {Λ' : Type u} [AddCommGroup Λ'] (g : Λ' →+ Λ)

/-- Restriction of characters along `g : Λ' →+ Λ`, a natural homomorphism
`Hom(Λ, Bˣ) → Hom(Λ', Bˣ)`. -/
def restrict : functor R Λ ⟶ functor R Λ' where
  app B := GrpCat.ofHom
    { toFun := fun χ => (χ : Multiplicative Λ →* Bˣ).comp (AddMonoidHom.toMultiplicative g)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem restrict_app_apply {B : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Bˣ)
    (m : Multiplicative Λ') :
    DFunLike.coe (F := Multiplicative Λ' →* Bˣ) ((restrict R g).app B χ) m =
      χ (.ofAdd (g m.toAdd)) :=
  rfl

/-- The algebra map `R[Λ'] → R[Λ]` induced by `g`. -/
abbrev incl : algebra R Λ' ⟶ algebra R Λ :=
  lift R Λ' ((monomialUnits R Λ).comp (AddMonoidHom.toMultiplicative g))

@[simp] theorem incl_single (γ : Λ') (r : R) :
    (incl R g).hom (AddMonoidAlgebra.single γ r) = AddMonoidAlgebra.single (g γ) r := by
  rw [lift_single]
  change r • AddMonoidAlgebra.single (g γ) (1 : R) = _
  rw [AddMonoidAlgebra.smul_single', mul_one]

theorem incl_apply (x : AddMonoidAlgebra R Λ') :
    (incl R g).hom x = AddMonoidAlgebra.mapDomain g x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp [AddMonoidAlgebra.mapDomain_zero]
  | add x y hx hy => rw [map_add, hx, hy, AddMonoidAlgebra.mapDomain_add]
  | single γ r => rw [incl_single, AddMonoidAlgebra.mapDomain_single]

theorem incl_injective (hg : Function.Injective g) : Function.Injective (incl R g).hom := by
  intro x y hxy
  rw [incl_apply, incl_apply] at hxy
  exact AddMonoidAlgebra.mapDomain_injective hg hxy

/-- Restricted characters are classified by `incl g` followed by the original classifying map. -/
theorem homEquiv_symm_restrict {B : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Bˣ) :
    (corepresentation R Λ').homEquiv.symm ((restrict R g).app B χ) =
      incl R g ≫ (corepresentation R Λ).homEquiv.symm χ := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro γ
    change (lift R Λ' _).hom _ = (lift R Λ χ).hom ((incl R g).hom _)
    rw [incl_single]
    erw [lift_single, lift_single]
    rfl
  · exact Subsingleton.elim _ _

/-- The algebra map `incl g` intertwines the comultiplications. -/
theorem comul_incl :
    Corepresented.LinearEmbedding.comul (grpCorepresentation R Λ') ≫
        Corepresented.tensorLift (incl R g ≫ Corepresented.inl _ _)
          (incl R g ≫ Corepresented.inr _ _) =
      incl R g ≫ Corepresented.LinearEmbedding.comul (grpCorepresentation R Λ) := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro γ
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply]
    rw [incl_single]
    erw [comul_single, comul_single]
    rw [Corepresented.tensorLift_tmul]
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply]
    rw [incl_single, Corepresented.inl_apply, Corepresented.inr_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  · exact Subsingleton.elim _ _

/-- Restriction of the character `e(f)` classified by `f` is classified by `incl g ≫ f`. -/
theorem restrict_homEquiv {B : CommAlgCat.{u} R} (f : algebra R Λ ⟶ B) :
    (restrict R g).app B ((corepresentation R Λ).homEquiv f) =
      (corepresentation R Λ').homEquiv (incl R g ≫ f) := by
  rw [← Equiv.symm_apply_eq]
  erw [homEquiv_symm_restrict]
  rw [Equiv.symm_apply_apply]

end Restrict

/-! ### Split tori -/

section Split

variable {Λ} {I : Type u} [Fintype I] [DecidableEq I] (b : Λ ≃+ (I → ℤ))

/-- After choosing an isomorphism `Λ ≃ ℤ^I`, characters of `Λ` with values in a commutative
group `M` are `I`-indexed families in `M`. -/
def charEquiv (M : Type*) [CommGroup M] : (Multiplicative Λ →* M) ≃* (I → M) where
  toFun χ i := χ (.ofAdd (b.symm (Pi.single i 1)))
  invFun t :=
    { toFun := fun m => ∏ i, t i ^ (b m.toAdd i)
      map_one' := by simp
      map_mul' := fun m n => by
        simp only [toAdd_mul, map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib] }
  left_inv χ := by
    apply MonoidHom.ext
    intro m
    have hm : m = ∏ i, (Multiplicative.ofAdd (b.symm (Pi.single i 1))) ^ (b m.toAdd i) := by
      apply Multiplicative.toAdd.injective
      apply b.injective
      rw [toAdd_prod, map_sum]
      funext j
      simp [toAdd_zpow, map_zsmul, Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hm]
    simp [map_prod, map_zpow]
  right_inv t := by
    funext j
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, AddEquiv.apply_symm_apply]
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  map_mul' χ ψ := rfl

theorem charEquiv_apply (M : Type*) [CommGroup M] (χ : Multiplicative Λ →* M) (i : I) :
    charEquiv b M χ i = χ (.ofAdd (b.symm (Pi.single i 1))) :=
  rfl

/-- Points of `D(Λ)` over a test scheme, as `I`-indexed families of global units. -/
def splitPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (groupScheme R Λ).X) ≃* (I → (Γ(T.left, ⊤))ˣ) :=
  (Corepresented.pointsEquiv (functor R Λ) (grpCorepresentation R Λ) T).trans
    (charEquiv b ((algΓ R).obj T).unopˣ)

theorem splitPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme R Λ).X) :
    splitPointsEquiv R b T' (a ≫ x) =
      splitTorus.unitsRestrict I a (splitPointsEquiv R b T x) := by
  change charEquiv b _ (Corepresented.pointsEquiv (functor R Λ) (grpCorepresentation R Λ) T'
    (a ≫ x)) = _
  erw [Corepresented.pointsEquiv_naturality]
  rfl

/-- A choice of isomorphism `Λ ≃ ℤ^I` identifies `D(Λ)` with the split torus `𝔾_m^I`. -/
def splitIso : (groupScheme R Λ).toGrp ≅ splitTorus (Spec R) I :=
  isoOfPointModels (fun T : Over (Spec R) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => splitTorus.unitsRestrict I a) (splitPointsEquiv R b)
    (fun T => splitTorus.pointsEquiv I T) (splitPointsEquiv_naturality R b)
    (fun a y => splitTorus.pointsEquiv_naturality I a y)

include b in
theorem isSplitTorus : IsSplitTorus (groupScheme R Λ).toGrp :=
  ⟨I, inferInstance, ⟨splitIso R b⟩⟩

end Split

end Langlands.GroupScheme.Diagonalizable
