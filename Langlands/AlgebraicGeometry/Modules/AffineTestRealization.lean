import Langlands.AlgebraicGeometry.Modules.CoherentPresheafRealization
import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Quasicoherent

/-! # Module sheaves from compatible modules on all affine tests

An `AffineTestSystem S` assigns to every morphism `a : Spec R ⟶ S` an `R`-module `obj a`, and to
every algebra `R → A` with `Spec A ⟶ Spec R ⟶ S` equal to `b` a canonical `A`-linear
identification `A ⊗[R] obj a ≃ obj b`, compatible with composition of algebra maps.

Such a system is realized as an actual sheaf of `𝒪_S`-modules `E.toModules`, whose sections
over an affine open `U` are `obj` of the canonical chart `Spec Γ(S, U) ⟶ S`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

/-- Modules on all affine tests of a scheme `S`, with canonical coefficient-extension
identifications that are compatible under composition. -/
structure AffineTestSystem (S : Scheme.{u}) where
  /-- The module attached to an affine test `a : Spec R ⟶ S`. -/
  obj : ∀ {R : CommRingCat.{u}}, (Spec R ⟶ S) → ModuleCat.{u} R
  /-- The coefficient-extension identification along an algebra `R → A`. -/
  ext : ∀ {R A : CommRingCat.{u}} [Algebra R A] {a : Spec R ⟶ S} {b : Spec A ⟶ S},
    Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b → (A ⊗[R] obj a ≃ₗ[A] obj b)
  /-- Compatibility of the identifications with a tower of algebras. -/
  ext_comp : ∀ {R A B : CommRingCat.{u}} [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] {a : Spec R ⟶ S} {b : Spec A ⟶ S} {c : Spec B ⟶ S}
    (hab : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b)
    (hbc : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ b = c)
    (hac : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ a = c) (x : obj a),
    ext hac (1 ⊗ₜ x) = ext hbc (1 ⊗ₜ ext hab (1 ⊗ₜ x))

namespace AffineTestSystem

variable {S : Scheme.{u}} (E : AffineTestSystem S)

section Map

variable {R A B : CommRingCat.{u}}

/-- Coefficient extension along a ring map, `x ↦ 1 ⊗ x`. -/
def map (f : R ⟶ A) {a : Spec R ⟶ S} {b : Spec A ⟶ S} (h : Spec.map f ≫ a = b) :
    E.obj a →ₛₗ[f.hom] E.obj b :=
  letI := f.hom.toAlgebra
  { toFun x := E.ext h (1 ⊗ₜ x)
    map_add' x y := by rw [TensorProduct.tmul_add, map_add]
    map_smul' r x := by
      change E.ext h (1 ⊗ₜ (r • x)) = f.hom r • E.ext h (1 ⊗ₜ x)
      rw [← TensorProduct.smul_tmul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one, Algebra.smul_def, mul_one]
      rfl }

lemma map_apply (f : R ⟶ A) {a : Spec R ⟶ S} {b : Spec A ⟶ S} (h : Spec.map f ≫ a = b)
    (x : E.obj a) : E.map f h x = (letI := f.hom.toAlgebra; E.ext h (1 ⊗ₜ x)) :=
  rfl

lemma map_congr {f f' : R ⟶ A} (hf : f = f') {a : Spec R ⟶ S} {b : Spec A ⟶ S}
    (h : Spec.map f ≫ a = b) (h' : Spec.map f' ≫ a = b) (x : E.obj a) :
    E.map f h x = E.map f' h' x := by
  subst hf
  rfl

lemma map_comp (f : R ⟶ A) (g : A ⟶ B) {a : Spec R ⟶ S} {b : Spec A ⟶ S} {c : Spec B ⟶ S}
    (hab : Spec.map f ≫ a = b) (hbc : Spec.map g ≫ b = c) (hac : Spec.map (f ≫ g) ≫ a = c)
    (x : E.obj a) : E.map g hbc (E.map f hab x) = E.map (f ≫ g) hac x := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := (f ≫ g).hom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  exact (E.ext_comp hab hbc hac x).symm

/-- The value of the identification on a pure tensor. -/
lemma ext_tmul_toAlgebra (f : R ⟶ A) {a : Spec R ⟶ S} {b : Spec A ⟶ S}
    (h : Spec.map f ≫ a = b) (s : A) (x : E.obj a) :
    (letI := f.hom.toAlgebra; E.ext h (s ⊗ₜ x)) = s • E.map f h x := by
  let := f.hom.toAlgebra
  change E.ext h (s ⊗ₜ x) = s • E.ext h (1 ⊗ₜ x)
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Every element of the target is in the image of `map` after the identification along a
ring map whose underlying map is surjective. -/
lemma map_surjective (f : R ⟶ A) (hf : Function.Surjective f.hom) {a : Spec R ⟶ S}
    {b : Spec A ⟶ S} (h : Spec.map f ≫ a = b) : Function.Surjective (E.map f h) := by
  let := f.hom.toAlgebra
  intro y
  obtain ⟨z, rfl⟩ := (E.ext h).surjective y
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    obtain ⟨r, rfl⟩ := hf s
    refine ⟨r • x, ?_⟩
    rw [LinearMap.map_smulₛₗ, ← ext_tmul_toAlgebra]
  | add z z' hz hz' =>
    obtain ⟨x, hx⟩ := hz
    obtain ⟨x', hx'⟩ := hz'
    exact ⟨x + x', by rw [map_add, map_add, hx, hx']⟩

lemma map_id {a : Spec R ⟶ S} (h : Spec.map (𝟙 R) ≫ a = a) (x : E.obj a) :
    E.map (𝟙 R) h x = x := by
  have hidem : ∀ y, E.map (𝟙 R) h (E.map (𝟙 R) h y) = E.map (𝟙 R) h y := fun y =>
    (E.map_comp (𝟙 R) (𝟙 R) h h (by rw [Category.comp_id]; exact h) y).trans
      (E.map_congr (Category.comp_id _) _ _ y)
  obtain ⟨y, rfl⟩ := E.map_surjective (𝟙 R) (fun r => ⟨r, rfl⟩) h x
  exact hidem y

lemma map_eq_self (f : R ⟶ R) (hf : f = 𝟙 R) {a : Spec R ⟶ S} (h : Spec.map f ≫ a = a)
    (x : E.obj a) : E.map f h x = x := by
  subst hf
  exact E.map_id h x

/-- Along a localization away from `r`, coefficient extension is a localization of modules:
every element of the target is a pushed-forward element up to a power of `r`, and an element
killed by the extension is killed by a power of `r`. -/
lemma map_isLocalizedModule (f : R ⟶ A) (r : R)
    (hf : letI := f.hom.toAlgebra; IsLocalization.Away r A) {a : Spec R ⟶ S} {b : Spec A ⟶ S}
    (h : Spec.map f ≫ a = b) :
    (∀ y : E.obj b, ∃ (n : ℕ) (x : E.obj a), E.map f h x = f.hom (r ^ n) • y) ∧
      (∀ x : E.obj a, E.map f h x = 0 → ∃ n : ℕ, r ^ n • x = 0) := by
  let := f.hom.toAlgebra
  have : IsLocalization.Away r A := hf
  constructor
  · intro y
    obtain ⟨z, rfl⟩ := (E.ext h).surjective y
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj (r := r) (f := TensorProduct.mk R A (E.obj a) 1) z
    refine ⟨n, x, ?_⟩
    have hz : f.hom (r ^ n) • z = TensorProduct.mk R A (E.obj a) 1 x := by
      rw [← hx]
      exact algebraMap_smul A (r ^ n) z
    change E.ext h (1 ⊗ₜ x) = f.hom (r ^ n) • E.ext h z
    rw [← map_smul, hz]
    rfl
  · intro x hx
    have h0 : TensorProduct.mk R A (E.obj a) 1 x = TensorProduct.mk R A (E.obj a) 1 0 := by
      rw [map_zero]
      exact (E.ext h).injective ((show E.ext h (1 ⊗ₜ x) = 0 from hx).trans (map_zero _).symm)
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := r) h0
    exact ⟨n, by rw [hn, smul_zero]⟩

end Map

section Affine

/-- Restriction between affine opens. -/
def res {V W : S.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V) :
    E.obj hV.fromSpec →ₛₗ[(S.presheaf.map (homOfLE h).op).hom] E.obj hW.fromSpec :=
  E.map (S.presheaf.map (homOfLE h).op) (hV.map_fromSpec hW (homOfLE h).op)

lemma res_res {V W W' : S.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (h : W ≤ V) (h' : W' ≤ W) (x : E.obj hV.fromSpec) :
    E.res hW hW' h' (E.res hV hW h x) = E.res hV hW' (h'.trans h) x := by
  rw [res, res, res, E.map_comp _ _ _ _ (by rw [Spec.map_comp, Category.assoc,
    hV.map_fromSpec hW _, hW.map_fromSpec hW' _])]
  apply E.map_congr
  rw [← CategoryTheory.Functor.map_comp]
  rfl

lemma res_self {V : S.Opens} (hV : IsAffineOpen V) (h : V ≤ V) (x : E.obj hV.fromSpec) :
    E.res hV hV h x = x :=
  E.map_eq_self _
    (by rw [show (homOfLE h).op = 𝟙 (op V) from rfl, CategoryTheory.Functor.map_id]) _ x

lemma res_smul {V W : S.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (r : Γ(S, V)) (x : E.obj hV.fromSpec) :
    E.res hV hW h (r • x) = (S.presheaf.map (homOfLE h).op).hom r • E.res hV hW h x :=
  LinearMap.map_smulₛₗ _ r x

end Affine

section Presheaf

open CoherentPresheafRealization (AffBelow presheaf_res_res presheaf_res_refl)

/-- The component at an affine open `V ≤ O`, as a module over the functions on `O`. -/
abbrev famObj (O : S.Opens) (V : AffBelow O) : ModuleCat.{u} Γ(S, O) :=
  (ModuleCat.restrictScalars (S.presheaf.map (homOfLE V.2.2).op).hom).obj (E.obj V.2.1.fromSpec)

lemma famObj_smul (O : S.Opens) (V : AffBelow O) (r : Γ(S, O)) (x : E.famObj O V) :
    r • x = (show E.obj V.2.1.fromSpec from
      (S.presheaf.map (homOfLE V.2.2).op).hom r • (show E.obj V.2.1.fromSpec from x)) :=
  rfl

/-- Families over the affine opens below `O` that are compatible under restriction. -/
def compat (O : S.Opens) : Submodule Γ(S, O) (∀ V : AffBelow O, E.famObj O V) where
  carrier := {x | ∀ (V W : AffBelow O) (h : W.1 ≤ V.1), E.res V.2.1 W.2.1 h (x V) = x W}
  add_mem' {x y} hx hy V W h := by
    change E.res V.2.1 W.2.1 h (x V + y V) = x W + y W
    rw [map_add, hx, hy]
  zero_mem' V W h := map_zero (E.res V.2.1 W.2.1 h)
  smul_mem' r x hx V W h := by
    change E.res V.2.1 W.2.1 h ((S.presheaf.map (homOfLE V.2.2).op).hom r • x V) =
      (S.presheaf.map (homOfLE W.2.2).op).hom r • x W
    rw [res_smul, presheaf_res_res, hx]

/-- The member at `V` of a family over the affine opens below `O`. -/
abbrev famVal {O : S.Opens} (x : E.compat O) (V : AffBelow O) : E.obj V.2.1.fromSpec := x.1 V

lemma mem_compat {O : S.Opens} (x : E.compat O) (V W : AffBelow O) (h : W.1 ≤ V.1) :
    E.res V.2.1 W.2.1 h (E.famVal x V) = E.famVal x W :=
  x.2 V W h

/-- Evaluation of a compatible family at an affine open `U` itself. -/
def evalEquiv {U : S.Opens} (hU : IsAffineOpen U) : E.compat U ≃ₗ[Γ(S, U)] E.obj hU.fromSpec where
  toFun x := x.1 ⟨U, hU, le_rfl⟩
  invFun y := ⟨fun V => E.res hU V.2.1 V.2.2 y, fun V W h => E.res_res _ _ _ _ _ y⟩
  map_add' _ _ := rfl
  map_smul' r x := by
    rw [RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, famObj_smul]
    exact congrArg (fun s => s • (show E.obj hU.fromSpec from x.1 ⟨U, hU, le_rfl⟩))
      (presheaf_res_refl _ r)
  left_inv x := Subtype.ext <| funext fun V => E.mem_compat x ⟨U, hU, le_rfl⟩ V V.2.2
  right_inv y := E.res_self hU le_rfl y

lemma evalEquiv_apply {U : S.Opens} (hU : IsAffineOpen U) (x : E.compat U) :
    E.evalEquiv hU x = x.1 ⟨U, hU, le_rfl⟩ :=
  rfl

lemma evalEquiv_symm_apply {U : S.Opens} (hU : IsAffineOpen U) (y : E.obj hU.fromSpec)
    (V : AffBelow U) : ((E.evalEquiv hU).symm y).1 V = E.res hU V.2.1 V.2.2 y :=
  rfl

/-- Restriction of compatible families along `U ≤ U'`. -/
def compatRes {U U' : S.Opens} (h : U ≤ U') : E.compat U' →+ E.compat U where
  toFun x := ⟨fun V => x.1 ⟨V.1, V.2.1, V.2.2.trans h⟩, fun V W hWV =>
    x.2 ⟨V.1, V.2.1, V.2.2.trans h⟩ ⟨W.1, W.2.1, W.2.2.trans h⟩ hWV⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma compatRes_apply {U U' : S.Opens} (h : U ≤ U') (x : E.compat U') (V : AffBelow U) :
    (E.compatRes h x).1 V = x.1 ⟨V.1, V.2.1, V.2.2.trans h⟩ :=
  rfl

lemma compatRes_smul {U U' : S.Opens} (h : U ≤ U') (a : Γ(S, U')) (x : E.compat U') :
    E.compatRes h (a • x) = (S.presheaf.map (homOfLE h).op).hom a • E.compatRes h x := by
  apply Subtype.ext
  funext V
  change (S.presheaf.map (homOfLE (V.2.2.trans h)).op).hom a • x.1 ⟨V.1, V.2.1, V.2.2.trans h⟩ =
    (S.presheaf.map (homOfLE V.2.2).op).hom ((S.presheaf.map (homOfLE h).op).hom a) •
      x.1 ⟨V.1, V.2.1, V.2.2.trans h⟩
  rw [presheaf_res_res]

/-- The modules of compatible families, as a module presheaf over `Γ(S, ⊤)`. -/
def presheaf : OModulePresheaf (R := Γ(S, ⊤)) S.toSpecΓ where
  obj O := E.compat O
  addCommGroup _ := inferInstance
  module O :=
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (R := Γ(S, ⊤)) S.toSpecΓ O
    Module.compHom _ (algebraMap Γ(S, ⊤) Γ(S, O))
  moduleSections _ := inferInstance
  isScalarTower O := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom (R := Γ(S, ⊤)) S.toSpecΓ O
    let : Module Γ(S, ⊤) (E.compat O) := Module.compHom _ (algebraMap Γ(S, ⊤) Γ(S, O))
    exact ⟨fun r a x => by
      change (algebraMap Γ(S, ⊤) Γ(S, O) r * a) • x = algebraMap Γ(S, ⊤) Γ(S, O) r • a • x
      rw [mul_smul]⟩
  res {U U'} h :=
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (R := Γ(S, ⊤)) S.toSpecΓ U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (R := Γ(S, ⊤)) S.toSpecΓ U'
    letI : Module Γ(S, ⊤) (E.compat U) := Module.compHom _ (algebraMap Γ(S, ⊤) Γ(S, U))
    letI : Module Γ(S, ⊤) (E.compat U') := Module.compHom _ (algebraMap Γ(S, ⊤) Γ(S, U'))
    { E.compatRes h with
      map_smul' r x := by
        change E.compatRes h (algebraMap Γ(S, ⊤) Γ(S, U') r • x) =
          algebraMap Γ(S, ⊤) Γ(S, U) r • E.compatRes h x
        rw [compatRes_smul]
        congr 1
        exact (Scheme.TwoAffineOpenCover.restrictAlgHom (R := Γ(S, ⊤)) S.toSpecΓ h).commutes r }
  res_smul h a x := E.compatRes_smul h a x
  res_refl _ := rfl
  res_comp _ _ := rfl

lemma presheaf_res_apply {U U' : S.Opens} (h : U ≤ U') (x : E.compat U') :
    E.presheaf.res h (show E.presheaf.obj U' from x) = E.compatRes h x :=
  rfl

lemma evalEquiv_presheaf_res {U U' : S.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (h : U ≤ U') (x : E.compat U') :
    E.evalEquiv hU (E.compatRes h x) = E.res hU' hU h (E.evalEquiv hU' x) :=
  (E.mem_compat x ⟨U', hU', le_rfl⟩ ⟨U, hU, h⟩ h).symm

/-- The presheaf of compatible families is quasi-coherent. -/
theorem isQuasicoherent_presheaf : E.presheaf.IsQuasicoherent := by
  intro U f
  have hD : IsAffineOpen (S.basicOpen f) := U.2.basicOpen f
  obtain ⟨h1, h2⟩ := E.map_isLocalizedModule (S.presheaf.map (homOfLE (S.basicOpen_le f)).op) f
    (U.2.isLocalization_of_eq_basicOpen f (homOfLE (S.basicOpen_le f)) rfl)
    (U.2.map_fromSpec hD (homOfLE (S.basicOpen_le f)).op)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 (E.evalEquiv hD x)
    refine ⟨n, (E.evalEquiv U.2).symm y, (E.evalEquiv hD).injective ?_⟩
    rw [presheaf_res_apply, evalEquiv_presheaf_res _ hD U.2, LinearEquiv.apply_symm_apply,
      LinearEquiv.map_smul]
    exact hy
  · intro y hy
    obtain ⟨n, hn⟩ := h2 (E.evalEquiv U.2 y) (by
      change E.res U.2 hD (S.basicOpen_le f) (E.evalEquiv U.2 y) = 0
      rw [← E.evalEquiv_presheaf_res hD U.2]
      exact (congrArg (E.evalEquiv hD) hy).trans (map_zero _))
    exact ⟨n, (E.evalEquiv U.2).injective (by rw [LinearEquiv.map_smul, hn, map_zero])⟩

end Presheaf

section Realization

open CoherentPresheafRealization (AffBelow)

/-- The realization of an affine test system as a sheaf of `𝒪_S`-modules. -/
def toModules : S.Modules :=
  CoherentPresheafRealization.realization E.presheaf E.isQuasicoherent_presheaf

/-- The sections of the realization over an affine open `U` are the module attached to the
canonical chart `Spec Γ(S, U) ⟶ S` of `U`. -/
def sectionsEquiv {U : S.Opens} (hU : IsAffineOpen U) :
    Γ(E.toModules, U) ≃ₗ[Γ(S, U)] E.obj hU.fromSpec :=
  (CoherentPresheafRealization.sectionsEquiv E.isQuasicoherent_presheaf hU).trans
    (E.evalEquiv hU)

/-- The section identifications commute with restriction between affine opens. -/
lemma sectionsEquiv_naturality {U V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) (s : Γ(E.toModules, U)) :
    E.sectionsEquiv hV (E.toModules.presheaf.map (homOfLE h).op s) =
      E.res hU hV h (E.sectionsEquiv hU s) := by
  exact (congrArg (E.evalEquiv hV) (CoherentPresheafRealization.sectionsEquiv_naturality
    E.isQuasicoherent_presheaf hU hV h s)).trans (E.evalEquiv_presheaf_res hV hU h _)

/-- A section over an arbitrary open `O` from a family over the affine opens below `O` that is
compatible under restriction. -/
def ofFamily {O : S.Opens} (x : E.compat O) : Γ(E.toModules, O) :=
  (⟨fun V => (E.evalEquiv V.2.1).symm (E.famVal x V), fun V W h =>
      (E.evalEquiv W.2.1).injective <| (E.evalEquiv_presheaf_res W.2.1 V.2.1 h _).trans <| by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact E.mem_compat x V W h⟩ :
    CoherentPresheafRealization.compat E.presheaf O)

/-- The section built from a compatible family restricts on each affine open `V ≤ O` to the
member of the family at `V`. -/
lemma sectionsEquiv_res_ofFamily {O : S.Opens} (x : E.compat O) (V : AffBelow O) :
    E.sectionsEquiv V.2.1 (E.toModules.presheaf.map (homOfLE V.2.2).op (E.ofFamily x)) =
      E.famVal x V := by
  have h1 : CoherentPresheafRealization.sectionsEquiv E.isQuasicoherent_presheaf V.2.1
      (E.toModules.presheaf.map (homOfLE V.2.2).op (E.ofFamily x)) =
        (E.evalEquiv V.2.1).symm (E.famVal x V) :=
    CoherentPresheafRealization.sectionsEquiv_apply _ _ _
  exact (congrArg (E.evalEquiv V.2.1) h1).trans (LinearEquiv.apply_symm_apply _ _)

/-- The realization is quasi-coherent. -/
instance isQuasicoherent_toModules : E.toModules.IsQuasicoherent := by
  choose U hU hyU _ using fun y : S => exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  refine IntegralIdealFiltration.isQuasicoherent_of_affine_nbhds _ U hU hyU fun y => ?_
  have hW : IsAffineOpen ((hU y).fromSpec ''ᵁ ⊤) :=
    (isAffineOpen_top (Spec Γ(S, U y))).image_of_isOpenImmersion (hU y).fromSpec
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  exact CoherentPresheafRealization.isLocalizing_restrict (hU y).fromSpec _ hW

end Realization

end AffineTestSystem

end Langlands.AlgebraicGeometry.Modules
