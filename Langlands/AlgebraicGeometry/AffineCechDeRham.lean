import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Degree-one relative de Rham cohomology on an affine cover

The construction uses the relative Kähler differentials of the rings of sections
and the alternating Čech differential on tuples of cover indices. It implements
the total differential of Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, revised 14 March 2021, §2.1.6, pp. 129–130 and 132.
The first filtration step uses the truncation discussed on p. 135.
The retained source is `lan-2008-pel-thesis-revision-2021`, with SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

namespace RelativeForms

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Relative two-forms on an algebra are the second exterior power over that algebra. -/
abbrev Two (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :=
  ⋀[A]^2 Ω[A⁄R]

/-- The wedge product of two relative one-forms. -/
def wedge (x y : Ω[A⁄R]) : Two R A := exteriorPower.ιMulti A 2 ![x, y]

private lemma wedge_add_left (x y z : Ω[A⁄R]) :
    wedge (x + y) z = wedge x z + wedge y z :=
  (exteriorPower.ιMulti A 2).map_vecCons_add ![z] x y

private lemma wedge_smul_left (a : A) (x y : Ω[A⁄R]) :
    wedge (a • x) y = a • wedge x y :=
  (exteriorPower.ιMulti A 2).map_vecCons_smul ![y] a x

private lemma wedge_swap (x y : Ω[A⁄R]) : wedge y x = -wedge x y := by
  have h : (![x, y] : Fin 2 → Ω[A⁄R]) ∘ Equiv.swap 0 1 = ![y, x] := by
    funext i
    fin_cases i <;> rfl
  simpa only [wedge, h] using
    (exteriorPower.ιMulti A 2).map_swap ![x, y] (by decide : (0 : Fin 2) ≠ 1)

private lemma wedge_add_right (x y z : Ω[A⁄R]) :
    wedge x (y + z) = wedge x y + wedge x z := by
  rw [wedge_swap (y + z) x, wedge_add_left, wedge_swap x y, wedge_swap x z,
    neg_add, neg_neg, neg_neg]

private lemma wedge_smul_right (a : A) (x y : Ω[A⁄R]) :
    wedge x (a • y) = a • wedge x y := by
  rw [wedge_swap (a • y) x, wedge_smul_left, wedge_swap x y, smul_neg, neg_neg]

@[simp] private lemma wedge_zero_left (x : Ω[A⁄R]) : wedge 0 x = 0 := by
  simpa only [zero_smul] using wedge_smul_left (0 : A) x x

@[simp] private lemma wedge_zero_right (x : Ω[A⁄R]) : wedge x 0 = 0 := by
  rw [wedge_swap 0 x, wedge_zero_left, neg_zero]

/-- The universal derivation on functions, viewed as a base-linear map. -/
abbrev dZero (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : A →ₗ[R] Ω[A⁄R] :=
  (KaehlerDifferential.D R A).toLinearMap

private def freeDerivative : (A →₀ A) →ₗ[R] Two R A :=
  Finsupp.lsum R fun b =>
    ({ toFun := fun x => wedge x (KaehlerDifferential.D R A b)
       map_add' := fun x y => wedge_add_left x y _
       map_smul' := fun r x => by
         simp only [RingHom.id_apply, ← IsScalarTower.algebraMap_smul A r,
           wedge_smul_left] } : Ω[A⁄R] →ₗ[R] Two R A).comp (dZero R A)

private lemma freeDerivative_single (b a : A) :
    freeDerivative (R := R) (Finsupp.single b a) =
      wedge (KaehlerDifferential.D R A a) (KaehlerDifferential.D R A b) := by
  rw [freeDerivative, Finsupp.lsum_single]
  rfl

private def presentOne : (A →₀ A) →ₗ[R] Ω[A⁄R] :=
  (Finsupp.linearCombination A (KaehlerDifferential.D R A)).restrictScalars R

private lemma presentOne_surjective : Function.Surjective (presentOne (R := R) (A := A)) :=
  KaehlerDifferential.linearCombination_surjective R A

private lemma ker_presentOne_le : LinearMap.ker (presentOne (R := R) (A := A)) ≤
    LinearMap.ker (freeDerivative (R := R) (A := A)) := by
  intro z hz
  have hrel : z ∈ KaehlerDifferential.kerTotal R A :=
    (KaehlerDifferential.kerTotal_eq R A) ▸ hz
  change freeDerivative z = (0 : Two R A)
  rw [← one_smul A z]
  refine Submodule.span_induction
    (p := fun z _ => ∀ a : A, freeDerivative (a • z) = (0 : Two R A))
    ?_ ?_ ?_ ?_ hrel 1
  · rintro _ ((⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨r, rfl⟩) a
    · simp only [smul_sub, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one, map_sub,
        map_add, freeDerivative_single, wedge_add_right, sub_self]
    · simp only [smul_sub, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one, map_sub,
        map_add, freeDerivative_single, (KaehlerDifferential.D R A).leibniz,
        wedge_add_left, wedge_add_right, wedge_smul_left, wedge_smul_right]
      rw [wedge_swap (KaehlerDifferential.D R A x) (KaehlerDifferential.D R A y), smul_neg]
      abel
    · simp [Finsupp.smul_single, freeDerivative_single]
  · intro a
    simp
  · intro x y _ _ hx hy a
    rw [smul_add, map_add, hx, hy, add_zero]
  · intro a x _ hx b
    rw [smul_smul, hx]

/-- The exterior differential on one-forms, obtained by descending the map
`[b ↦ a] ↦ da ∧ db` through the Kähler differential relations. -/
def dOne (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Ω[A⁄R] →ₗ[R] Two R A :=
  presentOne.liftOfSurjective presentOne_surjective ⟨freeDerivative, ker_presentOne_le⟩

/-- The exterior differential sends `a db` to `da ∧ db`. -/
lemma dOne_smul_d (a b : A) :
    dOne R A (a • KaehlerDifferential.D R A b) =
      wedge (KaehlerDifferential.D R A a) (KaehlerDifferential.D R A b) := by
  have h : presentOne (Finsupp.single b a) = a • KaehlerDifferential.D R A b := by
    simp [presentOne]
  rw [← h, dOne, LinearMap.equivOfSurjective_apply, freeDerivative_single]

@[simp]
lemma dOne_dZero (a : A) : dOne R A (dZero R A a) = 0 := by
  change dOne R A (KaehlerDifferential.D R A a) = 0
  rw [← one_smul A (KaehlerDifferential.D R A a), dOne_smul_d]
  simp

section Maps

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- The map on relative one-forms induced by a homomorphism of base algebras. -/
def mapOne (f : A →ₐ[R] B) : Ω[A⁄R] →ₛₗ[f.toRingHom] Ω[B⁄R] := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algHom f
  let F := KaehlerDifferential.map R R A B
  exact
    { F.toAddMonoidHom with
      map_smul' := fun a ω => by
        change F (a • ω) = f a • F ω
        rw [F.map_smul, ← IsScalarTower.algebraMap_smul B a]
        rfl }

@[simp]
lemma mapOne_d (f : A →ₐ[R] B) (a : A) :
    mapOne f (KaehlerDifferential.D R A a) = KaehlerDifferential.D R B (f a) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algHom f
  exact KaehlerDifferential.map_D R R A B a

@[simp]
lemma mapOne_id (ω : Ω[A⁄R]) : mapOne (AlgHom.id R A) ω = ω := by
  change mapOne (AlgHom.id R A) ω = (LinearMap.id : Ω[A⁄R] →ₗ[A] Ω[A⁄R]) ω
  refine LinearMap.eqOn_span (s := Set.range (KaehlerDifferential.D R A)) ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact mapOne_d (AlgHom.id R A) a
  · rw [KaehlerDifferential.span_range_derivation]
    trivial

@[simp]
lemma mapOne_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (ω : Ω[A⁄R]) :
    mapOne (g.comp f) ω = mapOne g (mapOne f ω) := by
  let F : Ω[A⁄R] →ₛₗ[(g.comp f).toRingHom] Ω[C⁄R] := (mapOne g).comp (mapOne f)
  change mapOne (g.comp f) ω = F ω
  refine LinearMap.eqOn_span (s := Set.range (KaehlerDifferential.D R A)) ?_ ?_
  · rintro _ ⟨a, rfl⟩
    change mapOne (g.comp f) (KaehlerDifferential.D R A a) =
      mapOne g (mapOne f (KaehlerDifferential.D R A a))
    rw [mapOne_d, mapOne_d, mapOne_d]
    rfl
  · rw [KaehlerDifferential.span_range_derivation]
    trivial

private def alternatingTwo (f : A →ₐ[R] B) :
    letI : Module A (Two R B) := Module.compHom (Two R B) f.toRingHom
    Ω[A⁄R] [⋀^Fin 2]→ₗ[A] Two R B := by
  letI : Module A (Two R B) := Module.compHom (Two R B) f.toRingHom
  exact
    { toFun := fun v => exteriorPower.ιMulti B 2 (mapOne f ∘ v)
      map_update_add' := by
        intro _ v i x y
        simp only [Function.comp_update, (mapOne f).map_add, AlternatingMap.map_update_add]
      map_update_smul' := by
        intro _ v i a x
        change exteriorPower.ιMulti B 2 (mapOne f ∘ Function.update v i (a • x)) =
          f a • exteriorPower.ιMulti B 2 (mapOne f ∘ Function.update v i x)
        rw [Function.comp_update, Function.comp_update, (mapOne f).map_smulₛₗ,
          AlternatingMap.map_update_smul]
        rfl
      map_eq_zero_of_eq' := fun v _ _ h hne =>
        (exteriorPower.ιMulti B 2).map_eq_zero_of_eq _ (congrArg (mapOne f) h) hne }

/-- The map on relative two-forms induced by a homomorphism of base algebras. -/
def mapTwo (f : A →ₐ[R] B) : Two R A →ₛₗ[f.toRingHom] Two R B := by
  letI : Module A (Two R B) := Module.compHom (Two R B) f.toRingHom
  let F := exteriorPower.alternatingMapLinearEquiv (alternatingTwo f)
  exact { F.toAddMonoidHom with map_smul' := F.map_smul }

@[simp]
lemma mapTwo_ιMulti (f : A →ₐ[R] B) (v : Fin 2 → Ω[A⁄R]) :
    mapTwo f (exteriorPower.ιMulti A 2 v) = exteriorPower.ιMulti B 2 (mapOne f ∘ v) := by
  let : Module A (Two R B) := Module.compHom (Two R B) f.toRingHom
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (alternatingTwo f) v

@[simp]
lemma mapTwo_wedge (f : A →ₐ[R] B) (x y : Ω[A⁄R]) :
    mapTwo f (wedge x y) = wedge (mapOne f x) (mapOne f y) := by
  rw [wedge, mapTwo_ιMulti, wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp]
lemma mapTwo_id (ω : Two R A) : mapTwo (AlgHom.id R A) ω = ω := by
  change mapTwo (AlgHom.id R A) ω = (LinearMap.id : Two R A →ₗ[A] Two R A) ω
  refine LinearMap.eqOn_span (s := Set.range (exteriorPower.ιMulti A 2)) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    change mapTwo (AlgHom.id R A) (exteriorPower.ιMulti A 2 v) = exteriorPower.ιMulti A 2 v
    rw [mapTwo_ιMulti]
    exact congrArg (exteriorPower.ιMulti A 2) (funext fun i => mapOne_id (v i))
  · rw [exteriorPower.ιMulti_span]
    trivial

@[simp]
lemma mapTwo_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (ω : Two R A) :
    mapTwo (g.comp f) ω = mapTwo g (mapTwo f ω) := by
  let F : Two R A →ₛₗ[(g.comp f).toRingHom] Two R C := (mapTwo g).comp (mapTwo f)
  change mapTwo (g.comp f) ω = F ω
  refine LinearMap.eqOn_span (s := Set.range (exteriorPower.ιMulti A 2)) ?_ ?_
  · rintro _ ⟨v, rfl⟩
    change mapTwo (g.comp f) (exteriorPower.ιMulti A 2 v) =
      mapTwo g (mapTwo f (exteriorPower.ιMulti A 2 v))
    rw [mapTwo_ιMulti, mapTwo_ιMulti, mapTwo_ιMulti]
    exact congrArg (exteriorPower.ιMulti C 2) (funext fun i => mapOne_comp f g (v i))
  · rw [exteriorPower.ιMulti_span]
    trivial

/-- The exterior derivative commutes with the map on forms induced by an algebra homomorphism. -/
lemma dOne_natural (f : A →ₐ[R] B) (ω : Ω[A⁄R]) :
    dOne R B (mapOne f ω) = mapTwo f (dOne R A ω) := by
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R A ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, (mapOne f).map_smulₛₗ, mapOne_d,
      dOne_smul_d, dOne_smul_d, mapTwo_wedge, mapOne_d, mapOne_d]
    rfl
  | add x y hx hy =>
    rw [map_add, (mapOne f).map_add, map_add, map_add, (mapTwo f).map_add, hx, hy]

end Maps

end RelativeForms

section Coefficients

variable (R : Type u) [CommRing R]

private abbrev forgetToModules : CommAlgCat.{u} R ⥤ ModuleCat.{u} R :=
  forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

/-- A map semilinear over an `R`-algebra homomorphism is linear over `R`. -/
private def restrictBase {A B M N : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    [Module R M] [Module R N] [IsScalarTower R A M] [IsScalarTower R B N]
    (f : A →ₐ[R] B) (g : M →ₛₗ[f.toRingHom] N) : M →ₗ[R] N where
  toFun := g
  map_add' := g.map_add
  map_smul' r m := by
    change g (r • m) = r • g m
    rw [← IsScalarTower.algebraMap_smul A r m, g.map_smulₛₗ]
    exact (congrArg (· • g m) (f.commutes r)).trans (IsScalarTower.algebraMap_smul B r _)

private def oneFormModules : CommAlgCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R Ω[A⁄R]
  map g := ModuleCat.ofHom (restrictBase R g.hom (RelativeForms.mapOne g.hom))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun ω => RelativeForms.mapOne_id ω)
  map_comp g h := ModuleCat.hom_ext (LinearMap.ext fun ω => RelativeForms.mapOne_comp g.hom h.hom ω)

private def twoFormModules : CommAlgCat.{u} R ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (RelativeForms.Two R A)
  map g := ModuleCat.ofHom (restrictBase R g.hom (RelativeForms.mapTwo g.hom))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun ω => RelativeForms.mapTwo_id ω)
  map_comp g h := ModuleCat.hom_ext (LinearMap.ext fun ω => RelativeForms.mapTwo_comp g.hom h.hom ω)

private def universalDerivative : forgetToModules R ⟶ oneFormModules R where
  app A := ModuleCat.ofHom (RelativeForms.dZero R A)
  naturality {_ _} g :=
    ModuleCat.hom_ext (LinearMap.ext fun a => (RelativeForms.mapOne_d g.hom a).symm)

private def exteriorDerivative : oneFormModules R ⟶ twoFormModules R where
  app A := ModuleCat.ofHom (RelativeForms.dOne R A)
  naturality {_ _} g :=
    ModuleCat.hom_ext (LinearMap.ext fun ω => RelativeForms.dOne_natural g.hom ω)

end Coefficients

section Cech

open Langlands.Cohomology
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_comp)

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (U : Scheme.AffineOpenCover.{u} X)

/-- The open images of the members of the supplied cover. -/
abbrev coverOpens (i : U.I₀) : X.Opens := (U.f i).opensRange

/-- Every tuple intersection used by the Čech complex is affine. -/
lemma isAffineOpen_inter [IsSeparated f] {p : ℕ} (σ : Fin (p + 1) → U.I₀) :
    IsAffineOpen (inter (coverOpens U) σ) := by
  have : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  exact IsAffineOpen.iInf (fun j => AlgebraicGeometry.isAffineOpen_opensRange (U.f (σ j)))

/-- The section rings as a presheaf of commutative `R`-algebras. -/
def sectionAlgebras : (Opens X)ᵒᵖ ⥤ CommAlgCat.{u} R where
  obj V :=
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f V.unop
    CommAlgCat.of R Γ(X, V.unop)
  map {V W} i :=
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f V.unop
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f W.unop
    CommAlgCat.ofHom (Scheme.TwoAffineOpenCover.restrictAlgHom f (leOfHom i.unop))
  map_id V := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    change X.presheaf.map (𝟙 V) x = x
    rw [X.presheaf.map_id]
    rfl
  map_comp i j := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    change X.presheaf.map (i ≫ j) x = X.presheaf.map j (X.presheaf.map i x)
    rw [X.presheaf.map_comp]
    rfl

/-- The functions on opens, regarded as `R`-modules. -/
abbrev functions := sectionAlgebras f ⋙ forgetToModules R

/-- The relative Kähler differentials of the section rings, with their natural restrictions. -/
abbrev oneForms := sectionAlgebras f ⋙ oneFormModules R

/-- The relative exterior squares of the Kähler differentials of the section rings. -/
abbrev twoForms := sectionAlgebras f ⋙ twoFormModules R

/-- Componentwise universal derivation, as a map of presheaves of `R`-modules. -/
def exteriorD0 : functions f ⟶ oneForms f := Functor.whiskerLeft (sectionAlgebras f)
  (universalDerivative R)

/-- Componentwise exterior differential of relative one-forms. -/
def exteriorD1 : oneForms f ⟶ twoForms f := Functor.whiskerLeft (sectionAlgebras f)
  (exteriorDerivative R)

/-- Čech cochains indexed by all tuples, with entries on their intersections. -/
abbrev Cochains (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) : Type u :=
  ∀ σ : Fin (p + 1) → U.I₀, P.obj (op (inter (coverOpens U) σ))

private abbrev forgetAdd := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- The alternating coface restrictions, linear over the base. -/
def cechD (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) :
    Cochains U P p →ₗ[R] Cochains U P (p + 1) :=
  { Cech.d (P ⋙ forgetAdd (R := R)) (coverOpens U) p with
    map_smul' := fun r c => by
      funext τ
      change Cech.d (P ⋙ forgetAdd (R := R)) (coverOpens U) p (r • c) τ =
        r • (show P.obj (op (inter (coverOpens U) τ)) from
          Cech.d (P ⋙ forgetAdd (R := R)) (coverOpens U) p c τ)
      rw [Cech.d_apply, Cech.d_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      let ρ := (P.map (homOfLE (inter_le_comp (U := coverOpens U) τ j.succAbove)).op).hom
      change ((-1 : ℤ) ^ (j : ℕ)) • ρ (r • c (τ ∘ j.succAbove)) =
        r • (((-1 : ℤ) ^ (j : ℕ)) • ρ (c (τ ∘ j.succAbove)))
      rw [ρ.map_smul, smul_comm] }

/-- At a tuple, the Čech differential is the alternating sum of the restrictions from its faces. -/
lemma cechD_apply (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) (c : Cochains U P p)
    (τ : Fin (p + 2) → U.I₀) : cechD U P p c τ =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        P.map (homOfLE (inter_le_comp (U := coverOpens U) τ j.succAbove)).op
          (c (τ ∘ j.succAbove)) :=
  Cech.d_apply (P ⋙ forgetAdd (R := R)) (coverOpens U) p c τ

lemma cechD_cechD (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) (c : Cochains U P p) :
    cechD U P (p + 1) (cechD U P p c) = 0 :=
  Cech.d_d (P ⋙ forgetAdd (R := R)) (coverOpens U) p c

/-- The cochain map induced by a map of base-module presheaves. -/
def cochainMap {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R} (η : P ⟶ Q) (p : ℕ) :
    Cochains U P p →ₗ[R] Cochains U Q p :=
  LinearMap.pi fun σ => (η.app (op (inter (coverOpens U) σ))).hom.comp (LinearMap.proj σ)

@[simp]
lemma cochainMap_apply {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R} (η : P ⟶ Q) (p : ℕ)
    (c : Cochains U P p) (σ : Fin (p + 1) → U.I₀) :
    cochainMap U η p c σ = η.app (op (inter (coverOpens U) σ)) (c σ) := rfl

lemma cechD_cochainMap {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R} (η : P ⟶ Q) (p : ℕ)
    (c : Cochains U P p) : cechD U Q p (cochainMap U η p c) =
      cochainMap U η (p + 1) (cechD U P p c) :=
  Cech.d_map (coverOpens U) (Functor.whiskerRight η (forgetAdd (R := R))) p c

/-- The term of total degree zero. -/
abbrev C0 := Cochains U (functions f) 0

/-- The Čech functions and relative one-forms of total degree one. -/
abbrev C1 := Cochains U (functions f) 1 × Cochains U (oneForms f) 0

/-- The Čech functions, one-forms and two-forms of total degree two. -/
abbrev C2 := Cochains U (functions f) 2 × Cochains U (oneForms f) 1 × Cochains U (twoForms f) 0

/-- The total differential `h ↦ (∂h, dh)`. -/
def D0 : C0 f U →ₗ[R] C1 f U :=
  (cechD U (functions f) 0).prod (cochainMap U (exteriorD0 f) 0)

/-- The total differential `(a,b) ↦ (∂a, ∂b - da, db)`. -/
def D1 : C1 f U →ₗ[R] C2 f U :=
  let a := LinearMap.fst R (Cochains U (functions f) 1) (Cochains U (oneForms f) 0)
  let b := LinearMap.snd R (Cochains U (functions f) 1) (Cochains U (oneForms f) 0)
  ((cechD U (functions f) 1).comp a).prod
    (((cechD U (oneForms f) 0).comp b - (cochainMap U (exteriorD0 f) 1).comp a).prod
      ((cochainMap U (exteriorD1 f) 0).comp b))

@[simp]
lemma D0_apply (h : C0 f U) :
    D0 f U h = (cechD U (functions f) 0 h, cochainMap U (exteriorD0 f) 0 h) := rfl

@[simp]
lemma D1_apply (x : C1 f U) :
    D1 f U x = (cechD U (functions f) 1 x.1,
      cechD U (oneForms f) 0 x.2 - cochainMap U (exteriorD0 f) 1 x.1,
      cochainMap U (exteriorD1 f) 0 x.2) := rfl

/-- The two successive total differentials compose to zero. -/
lemma D1_comp_D0 : (D1 f U).comp (D0 f U) = 0 := by
  refine LinearMap.ext fun h => ?_
  change D1 f U (D0 f U h) = 0
  rw [D0_apply, D1_apply, cechD_cechD, cechD_cochainMap, sub_self]
  refine Prod.ext rfl (Prod.ext rfl (funext fun σ => ?_))
  exact RelativeForms.dOne_dZero (R := R)
    (A := (sectionAlgebras f).obj (op (inter (coverOpens U) σ))) (h σ)

/-- Degree-one cocycles of the total complex. -/
abbrev cocycles : Submodule R (C1 f U) := (D1 f U).ker

/-- The degree-zero differential with codomain restricted to cocycles. -/
def boundaryMap : C0 f U →ₗ[R] cocycles f U :=
  LinearMap.codRestrict (cocycles f U) (D0 f U) fun h =>
    LinearMap.mem_ker.mpr (LinearMap.congr_fun (D1_comp_D0 f U) h)

/-- The degree-one boundaries as a submodule of cocycles. -/
def boundaries : Submodule R (cocycles f U) := (boundaryMap f U).range

/-- Degree-one relative Čech–de Rham cohomology for the supplied affine cover. -/
abbrev H1 [Smooth f] [IsSeparated f] [Finite U.I₀] : Type u :=
  cocycles f U ⧸ boundaries f U

/-- Compatible one-forms whose exterior differential vanishes on every chart. -/
def closedForms : Submodule R (Cochains U (oneForms f) 0) :=
  (cechD U (oneForms f) 0).ker ⊓ (cochainMap U (exteriorD1 f) 0).ker

variable [Smooth f] [IsSeparated f] [Finite U.I₀]

/-- Send a compatible family of closed one-forms to its class in the total complex. -/
def closedFormClass : closedForms f U →ₗ[R] H1 f U :=
  (boundaries f U).mkQ.comp (LinearMap.codRestrict (cocycles f U)
    ((0 : closedForms f U →ₗ[R] Cochains U (functions f) 1).prod (closedForms f U).subtype)
    (fun b => by
      have hb := b.property
      change cechD U (oneForms f) 0 b.val = 0 ∧ cochainMap U (exteriorD1 f) 0 b.val = 0 at hb
      change D1 f U (0, b.val) = 0
      rw [D1_apply, map_zero, map_zero, sub_zero, hb.1, hb.2]
      rfl))

/-- The first Hodge filtration step in degree one, the image of the closed-form class map. -/
def hodgeF1 : Submodule R (H1 f U) := (closedFormClass f U).range

end Cech

end Langlands.AlgebraicGeometry.AffineCechDeRham
