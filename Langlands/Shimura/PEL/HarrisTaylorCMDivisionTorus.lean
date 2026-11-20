import Langlands.AbelianScheme.RationalBaseChange
import Langlands.AbelianScheme.RelativeHomNeronExtension
import Langlands.GroupScheme.Torus.Lattice
import Langlands.Shimura.Unitary.DivisionCondition

/-! # Cocharacters in the division case of Harris CM reduction -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Langlands.AbelianScheme Langlands.GroupScheme
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

section Specialization

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]

local notation "j" => NeronModelInfra.specGenericFibreInclusion V K
local notation "generic" => CommGroupScheme.baseChange j

/-- Endomorphisms of a supplied commutative Néron model are determined by,
and include extensions of, all the endomorphisms of its generic fibre. -/
private theorem neronGenericEnd_bijective
    (N : CommGroupScheme (Spec (CommRingCat.of V)))
    (hN : NeronModelInfra.NeronModelPropertyBundle V K N.X.hom) :
    Function.Bijective ((generic).mapEnd (X := N)) := by
  let : Smooth N.X.hom := hN.smooth
  let : IsSeparated N.X.hom := hN.separated
  constructor
  · intro f g hfg
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact genericFibre_map_injective K (congrArg
      (fun t : End ((generic).obj N) => (CommGroupScheme.groupHom t).hom.hom) hfg)
  · intro ψ
    let v := (CommGroupScheme.groupHom ψ).hom.hom
    let v' : NeronModelInfra.SchemeHomOver
        (pullback.snd N.X.hom j) (pullback.snd N.X.hom j) :=
      ⟨v.left, Over.w v⟩
    obtain ⟨φ, hφ⟩ := (hN.neronMapping N.X.left N.X.hom hN.smooth).2 v'
    let φ' : N.X ⟶ N.X := Over.homMk φ.1 φ.2
    have hmap : (Over.pullback j).map φ' = v := by
      apply Over.OverMorphism.ext
      have hleft := congrArg Subtype.val hφ
      change (NeronModelInfra.genericFibreRestrict V K N.X.hom N.X.hom φ).1 = v.left at hleft
      rw [← hleft]
      apply pullback.hom_ext
      · simp [NeronModelInfra.genericFibreRestrict, φ']
      · simp [NeronModelInfra.genericFibreRestrict, φ']
    have : IsMonHom ((Over.pullback j).map φ') := by
      rw [hmap]
      dsimp [v]
      infer_instance
    have hflat₁ : Flat (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := by
      rw [Over.tensorUnit_hom]
      exact MorphismProperty.id_mem @Flat _
    have hflat₂ : Flat (N.X ⊗ N.X).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have : IsMonHom φ' :=
      isMonHom_of_map (Over.pullback j) φ'
        (fun _ _ hf => genericFibre_map_injective K hf)
        (fun _ _ hf => genericFibre_map_injective K hf)
    refine ⟨Additive.ofMul (Grp.homMk φ'), ?_⟩
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact hmap

/-- Generic fibre of rational endomorphisms of a supplied Néron model. -/
private def neronGenericEnd0Equiv
    (N : CommGroupScheme (Spec (CommRingCat.of V)))
    (hN : NeronModelInfra.NeronModelPropertyBundle V K N.X.hom) :
    Rationalization.End N ≃ₐ[ℚ] Rationalization.End ((generic).obj N) := by
  let F := generic
  let e : End N ≃ₗ[ℤ] End (F.obj N) :=
    LinearEquiv.ofBijective (F.mapLinearMap ℤ) (neronGenericEnd_bijective K N hN)
  let eQ : Rationalization.End N ≃ₗ[ℚ] Rationalization.End (F.obj N) :=
    e.baseChange ℤ ℚ _ _
  let f : Rationalization.End N →ₐ[ℚ] Rationalization.End (F.obj N) :=
    Rationalization.liftEnd (F ⋙ Rationalization.inclusion) N
  refine AlgEquiv.ofBijective f ?_
  have hf : (f : Rationalization.End N → Rationalization.End (F.obj N)) = eQ := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul q g =>
      change q • ((1 : ℚ) ⊗ₜ[ℤ] F.map g) = q ⊗ₜ[ℤ] F.map g
      simp [TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact hf ▸ eQ.bijective

private def forgetAbelianScheme (S : Scheme) : AbelianScheme S ⥤ CommGroupScheme S where
  obj B := B.toCommGroupScheme
  map f := commHom f

private instance forgetAbelianScheme_additive (S : Scheme) :
    (forgetAbelianScheme S).Additive where
  map_add := by intros; rfl

/-- Transport of endomorphisms along an actual isomorphism. -/
private def endConj {C : Type*} [Category C] [Preadditive C] [Linear ℚ C]
    {X Y : C} (e : X ≅ Y) : End X →ₐ[ℚ] End Y where
  toFun f := e.inv ≫ f ≫ e.hom
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by
    change e.inv ≫ ((f + g) ≫ e.hom) = (e.inv ≫ f ≫ e.hom) + (e.inv ≫ g ≫ e.hom)
    rw [Preadditive.add_comp, Preadditive.comp_add]
  map_mul' f g := by
    change e.inv ≫ (g ≫ f) ≫ e.hom = (e.inv ≫ g ≫ e.hom) ≫ e.inv ≫ f ≫ e.hom
    simp [Category.assoc]
  commutes' q := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change e.inv ≫ (q • 𝟙 X) ≫ e.hom = q • 𝟙 Y
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.inv_hom_id]

/-- The action of generic-fibre rational endomorphisms on rational cocharacters
in the fibre of a supplied Néron model over a field-valued point. -/
def neronFibreCocharacterAction
    (N : CommGroupScheme (Spec (CommRingCat.of V)))
    (hN : NeronModelInfra.NeronModelPropertyBundle V K N.X.hom)
    {B : AbelianScheme (Spec (CommRingCat.of K))}
    (e : B.toCommGroupScheme ≅ (generic).obj N)
    {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of V)) :
    End0 B →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] cocharacterLattice ((CommGroupScheme.baseChange s).obj N)) :=
  let Nsp := (CommGroupScheme.baseChange s).obj N
  let f : End0 B →ₐ[ℚ] Rationalization.End B.toCommGroupScheme :=
    Rationalization.liftEnd
      (forgetAbelianScheme (Spec (CommRingCat.of K)) ⋙ Rationalization.inclusion) B
  let er : Rationalization.of B.toCommGroupScheme ≅
      Rationalization.of ((generic).obj N) :=
    Rationalization.inclusion.mapIso e
  let c : Rationalization.End B.toCommGroupScheme →ₐ[ℚ]
      Rationalization.End ((generic).obj N) :=
    endConj er
  let g := (neronGenericEnd0Equiv K N hN).symm.toAlgHom
  let sp : Rationalization.End N →ₐ[ℚ] Rationalization.End Nsp :=
    Rationalization.liftEnd (CommGroupScheme.baseChange s ⋙ Rationalization.inclusion) N
  (Rationalization.postAction (Gm (Spec (CommRingCat.of k))) Nsp).comp
    (sp.comp (g.comp (c.comp f)))

end Specialization

section Dimension

open NumberField _root_.Algebra

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A]
  [Algebra ℚ A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

/-- The actual algebra has twice the dimension of a normalized Harris abelian variety. -/
theorem harris_algebra_finrank (D : CentralSimpleUnitaryData E F A n) :
    Module.finrank ℚ A = 2 * (Module.finrank ℚ E * n ^ 2) := by
  let : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq
    (fun q => (map_ratCast (algebraMap E F) q).symm)
  rw [← Module.finrank_mul_finrank ℚ F A, D.dimension,
    ← Module.finrank_mul_finrank ℚ E F, IsQuadraticExtension.finrank_eq_two E F]
  ring

/-- If the rational cocharacters of the supplied Néron fibre have rank bounded
by the normalized Harris dimension, the division action forces them to vanish. -/
theorem subsingleton_neronFibreCocharacters
    (hD : D.IsDivision)
    {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {K : Type} [Field K] [Algebra V K] [IsFractionRing V K]
    (N : CommGroupScheme (Spec (CommRingCat.of V)))
    (hN : NeronModelInfra.NeronModelPropertyBundle V K N.X.hom)
    {B : AbelianScheme (Spec (CommRingCat.of K))}
    (e : B.toCommGroupScheme ≅ (CommGroupScheme.baseChange
      (NeronModelInfra.specGenericFibreInclusion V K)).obj N)
    (a : A →ₐ[ℚ] End0 B)
    {k : Type} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of V))
    [Module.Finite ℚ (ℚ ⊗[ℤ] cocharacterLattice ((CommGroupScheme.baseChange s).obj N))]
    (hrank : Module.finrank ℚ
      (ℚ ⊗[ℤ] cocharacterLattice ((CommGroupScheme.baseChange s).obj N)) ≤
      Module.finrank ℚ E * n ^ 2) :
    Subsingleton (ℚ ⊗[ℤ] cocharacterLattice ((CommGroupScheme.baseChange s).obj N)) := by
  let M := ℚ ⊗[ℤ] cocharacterLattice ((CommGroupScheme.baseChange s).obj N)
  let ρ := (neronFibreCocharacterAction K N hN e s).comp a
  let : Module A M := Module.compHom M ρ.toRingHom
  let : IsScalarTower ℚ A M := ⟨fun q b m => by
    change ρ (q • b) m = q • ρ b m
    rw [Algebra.smul_def, map_mul, ρ.commutes]
    rfl⟩
  apply D.subsingleton_of_finrank_lt hD
  have hpos : 0 < Module.finrank ℚ E * n ^ 2 :=
    Nat.mul_pos Module.finrank_pos (pow_pos (Nat.zero_lt_of_lt D.rank_gt_one) _)
  rw [harris_algebra_finrank D]
  omega

end Dimension

end Langlands.Shimura.HarrisTaylor
