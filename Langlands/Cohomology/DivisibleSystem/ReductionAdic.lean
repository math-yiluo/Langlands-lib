import Langlands.Cohomology.DivisibleSystem.Reduction
import Langlands.Coefficients.AdicTensorComparison

/-!
# Reductions as ideal-adic quotients and as tensor products

The published `reductionTower ℓ L` models Harris's inverse system `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` by the
cokernels `L / ℓ ^ m L` of multiplication by `ℓ ^ m`. This file compares it with the published
quotient system `Langlands.Coefficients.AdicSystem.system I L` of `L / I ^ m L` and with its
tensor presentation `(R / I ^ m) ⊗_R L`, where `I = (ℓ)`.

* `reductionTowerFunctor ℓ` is `L ↦ reductionTower ℓ L` as a functor.
* `reductionTowerCompIso ℓ F L` transports the tower along an additive functor `F` preserving
  cokernels; `reductionTowerFunctorCompIso` is its naturality in `L`.
* For an `R`-module `L`, `reductionAdicIso ℓ L m` identifies `L / ℓ ^ m L` with
  `L / (ℓ) ^ m L`; it sends the class of `x` to the class of `x`. These assemble into
  `reductionTowerAdicIso ℓ L` and `reductionTowerFunctorAdicIso ℓ R`.
* `reductionTowerFunctorTensorIso ℓ R` composes with the published `tensorFunctorIso`; at
  level `m` the class of `x` goes to `1 ⊗ x` (`reductionπ_reductionTensorIso_hom`).
* For representations, `reductionTowerForgetAdicIso ℓ X` compares the underlying modules of the
  tower of `X : Rep R G` with the quotient system of the underlying module of `X`, and
  `reductionTowerForgetAdicIso_hom_ρ` shows that the comparison carries the action on
  `X / ℓ ^ m X` to the action induced on the quotient.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u u' v'

namespace DivisibleSystem

section Functor

variable {C : Type u} [Category.{v} C] [Abelian C] (ℓ : ℕ)

/-- The tower `L ↦ {L / ℓ ^ m L}` as a functor `C ⥤ (ℕᵒᵖ ⥤ C)`. -/
@[simps]
def reductionTowerFunctor : C ⥤ (ℕᵒᵖ ⥤ C) where
  obj L := reductionTower ℓ L
  map f := reductionTowerMap ℓ f
  map_id _ := reductionTowerMap_id ℓ
  map_comp f g := reductionTowerMap_comp ℓ f g

end Functor

section Transport

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (ℓ : ℕ) (F : C ⥤ D) [F.Additive] [PreservesColimitsOfShape WalkingParallelPair F]

/-- An additive functor preserving cokernels sends `L / ℓ ^ m L` to `F L / ℓ ^ m F L`. -/
def reductionCompIso (L : C) (m : ℕ) :
    F.obj ((reductionTower ℓ L).obj (op m)) ≅ (reductionTower ℓ (F.obj L)).obj (op m) :=
  PreservesCokernel.iso F (powSMul ℓ m L) ≪≫ cokernelIsoOfEq (map_powSMul F ℓ m L)

/-- The comparison `reductionCompIso` is compatible with the projections. -/
@[reassoc (attr := simp)]
lemma map_reductionπ_reductionCompIso_hom (L : C) (m : ℕ) :
    F.map (reductionπ ℓ L m) ≫ (reductionCompIso ℓ F L m).hom = reductionπ ℓ (F.obj L) m := by
  change F.map (cokernel.π (powSMul ℓ m L)) ≫ (PreservesCokernel.iso F (powSMul ℓ m L)).hom ≫
    (cokernelIsoOfEq (map_powSMul F ℓ m L)).hom = cokernel.π (powSMul ℓ m (F.obj L))
  rw [PreservesCokernel.π_iso_hom_assoc, π_comp_cokernelIsoOfEq_hom]

/-- The inverse of `reductionCompIso` is compatible with the projections. -/
@[reassoc (attr := simp)]
lemma reductionπ_reductionCompIso_inv (L : C) (m : ℕ) :
    reductionπ ℓ (F.obj L) m ≫ (reductionCompIso ℓ F L m).inv = F.map (reductionπ ℓ L m) := by
  rw [Iso.comp_inv_eq, map_reductionπ_reductionCompIso_hom]

/-- The image under `F` of the tower of `L` is the tower of `F L`. -/
def reductionTowerCompIso (L : C) : reductionTower ℓ L ⋙ F ≅ reductionTower ℓ (F.obj L) :=
  NatIso.ofComponents (fun m => reductionCompIso ℓ F L m.unop) (by
    intro m n f
    induction m using Opposite.rec with | op m =>
    induction n using Opposite.rec with | op n =>
    rw [← cancel_epi (reductionCompIso ℓ F L m).inv,
      ← cancel_epi (reductionπ ℓ (F.obj L) m), Iso.inv_hom_id_assoc,
      reductionπ_reductionCompIso_inv_assoc, reductionπ_map]
    change F.map (reductionπ ℓ L m) ≫ F.map ((reductionTower ℓ L).map f) ≫ _ = _
    rw [← F.map_comp_assoc, reductionπ_map, map_reductionπ_reductionCompIso_hom])

/-- The components of `reductionTowerCompIso`. -/
@[simp]
lemma reductionTowerCompIso_hom_app (L : C) (m : ℕ) :
    (reductionTowerCompIso ℓ F L).hom.app (op m) = (reductionCompIso ℓ F L m).hom :=
  rfl

/-- The comparison `reductionCompIso` is natural in `L`. -/
@[reassoc]
lemma reductionCompIso_hom_naturality {L L' : C} (f : L ⟶ L') (m : ℕ) :
    F.map ((reductionTowerMap ℓ f).app (op m)) ≫ (reductionCompIso ℓ F L' m).hom =
      (reductionCompIso ℓ F L m).hom ≫ (reductionTowerMap ℓ (F.map f)).app (op m) := by
  rw [← cancel_epi (reductionCompIso ℓ F L m).inv,
    ← cancel_epi (reductionπ ℓ (F.obj L) m), Iso.inv_hom_id_assoc,
    reductionπ_reductionCompIso_inv_assoc, reductionπ_reductionTowerMap_app,
    ← F.map_comp_assoc, reductionπ_reductionTowerMap_app, F.map_comp_assoc,
    map_reductionπ_reductionCompIso_hom]

/-- `reductionTowerCompIso` is natural in `L`. -/
def reductionTowerFunctorCompIso :
    reductionTowerFunctor ℓ ⋙ (Functor.whiskeringRight ℕᵒᵖ C D).obj F ≅
      F ⋙ reductionTowerFunctor ℓ :=
  NatIso.ofComponents (reductionTowerCompIso ℓ F) (by
    intro L L' f
    refine NatTrans.ext (funext fun m => ?_)
    induction m using Opposite.rec with | op m =>
    exact reductionCompIso_hom_naturality ℓ F f m)

end Transport

section ModuleCat

variable (ℓ : ℕ) {R : Type u} [CommRing R]

/-- In a category of modules, multiplication by `ℓ ^ m` is scalar multiplication by the element
`ℓ ^ m` of `R`. -/
lemma powSMul_moduleCat_hom_apply (L : ModuleCat.{v} R) (m : ℕ) (x : L) :
    (powSMul ℓ m L).hom x = ((ℓ : R) ^ m) • x := by
  rw [powSMul, ModuleCat.hom_nsmul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow]

/-- The image of multiplication by `ℓ ^ m` is `(ℓ) ^ m L`. -/
lemma range_powSMul (L : ModuleCat.{v} R) (m : ℕ) :
    LinearMap.range (powSMul ℓ m L).hom =
      (Ideal.span {(ℓ : R)} ^ m • ⊤ : Submodule R L) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  ext x
  rw [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, powSMul_moduleCat_hom_apply]

/-- For an `R`-module `L`, the cokernel `L / ℓ ^ m L` of multiplication by `ℓ ^ m` is the
quotient `L / (ℓ) ^ m L` of the published ideal-adic system. -/
def reductionAdicIso (L : ModuleCat.{v} R) (m : ℕ) :
    (reductionTower ℓ L).obj (op m) ≅
      (Coefficients.AdicSystem.powerReduction (Ideal.span {(ℓ : R)}) m).obj L :=
  ModuleCat.cokernelIsoRangeQuotient (powSMul ℓ m L) ≪≫
    (Submodule.quotEquivOfEq _ _ (range_powSMul ℓ L m)).toModuleIso

/-- `reductionAdicIso` sends the class of `x` to the class of `x`. -/
@[reassoc (attr := simp)]
lemma reductionπ_reductionAdicIso_hom (L : ModuleCat.{v} R) (m : ℕ) :
    reductionπ ℓ L m ≫ (reductionAdicIso ℓ L m).hom =
      (Coefficients.AdicSystem.quotientMap (Ideal.span {(ℓ : R)}) m).app L := by
  ext x
  change (Submodule.quotEquivOfEq _ _ (range_powSMul ℓ L m))
    ((ModuleCat.cokernelIsoRangeQuotient (powSMul ℓ m L)).hom
      ((cokernel.π (powSMul ℓ m L)).hom x)) = Submodule.Quotient.mk x
  rw [ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply]
  rfl

/-- The comparisons `reductionAdicIso` are compatible with the transition maps. -/
@[reassoc]
lemma reductionAdicIso_hom_transition (L : ModuleCat.{v} R) {m n : ℕ} (h : m ≤ n) :
    (reductionTower ℓ L).map (homOfLE h).op ≫ (reductionAdicIso ℓ L m).hom =
      (reductionAdicIso ℓ L n).hom ≫
        (Coefficients.AdicSystem.transition (Ideal.span {(ℓ : R)}) h).app L := by
  rw [← cancel_epi (reductionπ ℓ L n), reductionπ_map_assoc, reductionπ_reductionAdicIso_hom,
    reductionπ_reductionAdicIso_hom_assoc, ← NatTrans.comp_app,
    Coefficients.AdicSystem.quotientMap_transition]

/-- For an `R`-module `L`, the tower of reductions `{L / ℓ ^ m L}` is the published ideal-adic
quotient system of `L` for the ideal `(ℓ)`. -/
def reductionTowerAdicIso (L : ModuleCat.{v} R) :
    reductionTower ℓ L ≅ Coefficients.AdicSystem.system (Ideal.span {(ℓ : R)}) L :=
  NatIso.ofComponents (fun m => reductionAdicIso ℓ L m.unop) (by
    intro n m f
    induction m using Opposite.rec with | op m =>
    induction n using Opposite.rec with | op n =>
    exact reductionAdicIso_hom_transition ℓ L (leOfHom f.unop))

/-- The components of `reductionTowerAdicIso`. -/
@[simp]
lemma reductionTowerAdicIso_hom_app (L : ModuleCat.{v} R) (m : ℕ) :
    (reductionTowerAdicIso ℓ L).hom.app (op m) = (reductionAdicIso ℓ L m).hom :=
  rfl

/-- The comparison `reductionAdicIso` is natural in `L`. -/
@[reassoc]
lemma reductionAdicIso_hom_naturality {L L' : ModuleCat.{v} R} (f : L ⟶ L') (m : ℕ) :
    (reductionTowerMap ℓ f).app (op m) ≫ (reductionAdicIso ℓ L' m).hom =
      (reductionAdicIso ℓ L m).hom ≫
        (Coefficients.AdicSystem.powerReduction (Ideal.span {(ℓ : R)}) m).map f := by
  rw [← cancel_epi (reductionπ ℓ L m), reductionTowerMap_app, reductionπ_reductionMap_assoc,
    reductionπ_reductionAdicIso_hom, reductionπ_reductionAdicIso_hom_assoc]
  exact (Coefficients.AdicSystem.quotientMap (Ideal.span {(ℓ : R)}) m).naturality f

variable (R) in
/-- The comparison of `reductionTowerAdicIso`, natural in the module: the functor
`L ↦ {L / ℓ ^ m L}` is the published `AdicSystem.functor (ℓ)`. -/
def reductionTowerFunctorAdicIso :
    reductionTowerFunctor ℓ ≅
      Coefficients.AdicSystem.functor.{u, v} (Ideal.span {(ℓ : R)}) :=
  NatIso.ofComponents (reductionTowerAdicIso ℓ) (by
    intro L L' f
    refine NatTrans.ext (funext fun m => ?_)
    induction m using Opposite.rec with | op m =>
    exact reductionAdicIso_hom_naturality ℓ f m)

/-- The components of `reductionTowerFunctorAdicIso`. -/
@[simp]
lemma reductionTowerFunctorAdicIso_hom_app_app (L : ModuleCat.{v} R) (m : ℕ) :
    ((reductionTowerFunctorAdicIso ℓ R).hom.app L).app (op m) = (reductionAdicIso ℓ L m).hom :=
  rfl

variable (R) in
/-- The functor `L ↦ {L / ℓ ^ m L}` is the tensor system `L ↦ {(R / (ℓ) ^ m) ⊗_R L}` of the
published `AdicSystem.tensorFunctor (ℓ)`, the levels viewed as `R`-modules. -/
def reductionTowerFunctorTensorIso :
    reductionTowerFunctor ℓ ≅ Coefficients.AdicSystem.tensorFunctor (Ideal.span {(ℓ : R)}) :=
  reductionTowerFunctorAdicIso.{u, u} ℓ R ≪≫
    (Coefficients.AdicSystem.tensorFunctorIso (Ideal.span {(ℓ : R)})).symm

/-- The level-`m` comparison `L / ℓ ^ m L ≅ (R / (ℓ) ^ m) ⊗_R L`. -/
def reductionTensorIso (L : ModuleCat.{u} R) (m : ℕ) :
    (reductionTower ℓ L).obj (op m) ≅
      (Coefficients.AdicSystem.tensorPower (Ideal.span {(ℓ : R)}) m).obj L :=
  ((reductionTowerFunctorTensorIso ℓ R).app L).app (op m)

/-- `reductionTensorIso` sends the class of `x` to `1 ⊗ x`: composed with the projection it is
the unit of the extension-restriction adjunction for `R ⟶ R / (ℓ) ^ m`. -/
@[reassoc (attr := simp)]
lemma reductionπ_reductionTensorIso_hom (L : ModuleCat.{u} R) (m : ℕ) :
    reductionπ ℓ L m ≫ (reductionTensorIso ℓ L m).hom =
      (ModuleCat.extendRestrictScalarsAdj
        (Ideal.Quotient.mk (Ideal.span {(ℓ : R)} ^ m))).unit.app L := by
  rw [← cancel_mono ((Coefficients.AdicSystem.tensorPowerIso (Ideal.span {(ℓ : R)}) m).hom.app L),
    ← NatTrans.comp_app, Coefficients.AdicSystem.tensorPowerIso_unit]
  change reductionπ ℓ L m ≫ ((reductionAdicIso ℓ L m).hom ≫
    ((Coefficients.AdicSystem.tensorPowerIso (Ideal.span {(ℓ : R)}) m).inv.app L)) ≫
      ((Coefficients.AdicSystem.tensorPowerIso (Ideal.span {(ℓ : R)}) m).hom.app L) = _
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, reductionπ_reductionAdicIso_hom]

end ModuleCat

section Rep

variable (ℓ : ℕ) {R : Type u} [CommRing R] {G : Type v} [Monoid G]

/-- For a representation `X`, the underlying modules of the tower `{X / ℓ ^ m X}` form the
published ideal-adic quotient system of the underlying module of `X` for the ideal `(ℓ)`. -/
def reductionTowerForgetAdicIso (X : Rep.{w} R G) :
    reductionTower ℓ X ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ≅
      Coefficients.AdicSystem.system (Ideal.span {(ℓ : R)})
        ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).obj X) :=
  reductionTowerCompIso ℓ (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) X ≪≫
    reductionTowerAdicIso ℓ _

/-- The comparison `reductionTowerForgetAdicIso` is compatible with the projections. -/
@[reassoc (attr := simp)]
lemma map_reductionπ_reductionTowerForgetAdicIso_hom (X : Rep.{w} R G) (m : ℕ) :
    (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map (reductionπ ℓ X m) ≫
        (reductionTowerForgetAdicIso ℓ X).hom.app (op m) =
      (Coefficients.AdicSystem.quotientMap (Ideal.span {(ℓ : R)}) m).app
        ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).obj X) := by
  change _ ≫ (reductionCompIso ℓ _ X m).hom ≫ (reductionAdicIso ℓ _ m).hom = _
  rw [map_reductionπ_reductionCompIso_hom_assoc, reductionπ_reductionAdicIso_hom]

/-- The comparison `reductionTowerForgetAdicIso` sends the class of `x` in `X / ℓ ^ m X` to the
class of `x` in `X / (ℓ) ^ m X`. -/
lemma reductionTowerForgetAdicIso_hom_reductionπ (X : Rep.{w} R G) (m : ℕ) (x : X) :
    ((reductionTowerForgetAdicIso ℓ X).hom.app (op m)).hom ((reductionπ ℓ X m).hom x) =
      Submodule.Quotient.mk x :=
  LinearMap.congr_fun
    (ModuleCat.hom_ext_iff.mp (map_reductionπ_reductionTowerForgetAdicIso_hom ℓ X m)) x

/-- The comparison `reductionTowerForgetAdicIso` carries the action of `g` on `X / ℓ ^ m X` to
the map induced on `X / (ℓ) ^ m X` by the action of `g` on `X`. -/
lemma reductionTowerForgetAdicIso_hom_ρ (X : Rep.{w} R G) (m : ℕ) (g : G)
    (y : (reductionTower ℓ X).obj (op m)) :
    ((reductionTowerForgetAdicIso ℓ X).hom.app (op m)).hom
        (((reductionTower ℓ X).obj (op m)).ρ g y) =
      ((Coefficients.AdicSystem.powerReduction (Ideal.span {(ℓ : R)}) m).map
        (ModuleCat.ofHom (X.ρ g))).hom
        (((reductionTowerForgetAdicIso ℓ X).hom.app (op m)).hom y) := by
  obtain ⟨x, rfl⟩ := (Rep.epi_iff_surjective (reductionπ ℓ X m)).mp inferInstance y
  rw [← Rep.hom_comm_apply, reductionTowerForgetAdicIso_hom_reductionπ,
    reductionTowerForgetAdicIso_hom_reductionπ]
  rfl

end Rep

end DivisibleSystem

end Langlands.Cohomology
