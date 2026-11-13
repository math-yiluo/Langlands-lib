import Langlands.AbelianScheme.Tate.RestrictedProductComparison

/-! # Actual prime Tate maps for rational homomorphisms -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj ModuleCat.Algebra

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme.Tate.PrimeAdic

universe u
variable {S : Scheme.{u}} (T : Over S) (p : ℕ) [Fact p.Prime]
  {A B C : AbelianScheme S}

/-- The actual prime Tate module as an additive functor on abelian schemes. -/
def rationalFunctor : AbelianScheme S ⥤ ModuleCat ℚ_[p] where
  obj A := ModuleCat.of ℚ_[p] (Rational A T p)
  map f := ModuleCat.ofHom (rationalMap T p f)
  map_id A := by apply ModuleCat.hom_ext; exact rationalMap_id T p
  map_comp f g := by apply ModuleCat.hom_ext; exact rationalMap_comp T p f g

instance : (rationalFunctor T p).Additive where
  map_add {_ _ f g} := by apply ModuleCat.hom_ext; exact rationalMap_add T p f g

/-- Extend the actual prime Tate functor to rationalized abelian schemes. -/
def rationalizedFunctor : Rationalization (AbelianScheme S) ⥤ ModuleCat ℚ_[p] :=
  Rationalization.lift (rationalFunctor T p)

/-- The actual prime Tate map associated to a rational homomorphism. -/
def rationalHomMap : Rationalization.Hom A B →ₗ[ℚ]
    (Rational A T p →ₗ[ℚ_[p]] Rational B T p) :=
  ModuleCat.homLinearEquiv.toLinearMap.comp
    (Rationalization.liftHom (rationalFunctor T p))

@[simp] theorem rationalHomMap_tmul (q : ℚ) (f : A ⟶ B) :
    rationalHomMap T p (q ⊗ₜ[ℤ] f) = q • rationalMap T p f := rfl

@[simp] theorem rationalHomMap_ofHom (f : A ⟶ B) :
    rationalHomMap T p (Rationalization.ofHom f) = rationalMap T p f := by
  simp

@[simp] theorem rationalHomMap_identity :
    rationalHomMap T p (Rationalization.identity A) = LinearMap.id := by
  simp [Rationalization.identity]

theorem rationalHomMap_comp (f : Rationalization.Hom A B)
    (g : Rationalization.Hom B C) :
    rationalHomMap T p (Rationalization.comp A B C f g) =
      (rationalHomMap T p g).comp (rationalHomMap T p f) :=
  congrArg ModuleCat.Hom.hom
    (Rationalization.liftHom_comp (rationalFunctor T p) f g)

/-- The actual rational endomorphism algebra acts on the actual prime Tate module. -/
def rationalEndAction (A : AbelianScheme S) :
    Rationalization.End A →ₐ[ℚ] Module.End ℚ_[p] (Rational A T p) where
  toRingHom := (ModuleCat.endRingEquiv ((rationalFunctor T p).obj A)).toRingHom.comp
    (Rationalization.liftEnd (rationalFunctor T p) A).toRingHom
  commutes' q := by
    change (Rationalization.liftEnd (rationalFunctor T p) A
      (algebraMap ℚ (Rationalization.End A) q)).hom = _
    rw [AlgHom.commutes]
    rfl

@[simp] theorem rationalEndAction_apply (A : AbelianScheme S)
    (f : Rationalization.End A) :
    rationalEndAction T p A f = rationalHomMap T p f := rfl

end Langlands.AbelianScheme.Tate.PrimeAdic

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

namespace Langlands.GroupScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
  (p : ℕ) [Fact p.Prime]

/-- Actual full rational Tate extraction onto a selected prime coordinate is surjective. -/
theorem rationalFullToPrime_surjective :
    Function.Surjective (rationalFullToPrime G T p) := by
  classical
  obtain ⟨e, he⟩ := rationalRestrictedProductComparison G T
  intro y
  let pi : Nat.Primes := ⟨p, Fact.out⟩
  let z : RationalRestrictedProduct G T :=
    RestrictedProduct.single
      (fun q : Nat.Primes => (PrimeAdic.integralImage G T (q : ℕ)).toAddSubgroup) pi y
  refine ⟨e.symm z, ?_⟩
  rw [← he _ pi, e.apply_symm_apply]
  exact RestrictedProduct.single_eq_same _ _ _

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (T : Over S) (P : ℕ → Prop) (p : ℕ) [Fact p.Prime]
  {A B : AbelianScheme S}

/-- Actual rational prime extraction commutes with rational homomorphisms. -/
theorem rationalToPrime_homMap (hP : ∀ n : ℕ, P (p ^ n))
    (f : Rationalization.Hom A B) (y : Rational A T P) :
    rationalToPrime B T P p hP (rationalHomMap T P f y) =
      PrimeAdic.rationalHomMap T p f (rationalToPrime A T P p hP y) := by
  induction f using TensorProduct.inductionOn with
  | tmul q f =>
    simp only [rationalHomMap_tmul, PrimeAdic.rationalHomMap_tmul,
      LinearMap.smul_apply, map_smul]
    exact congrArg (fun z => q • z)
      (LinearMap.congr_fun (rationalToPrime_map T P p hP f) y)
  | add f g hf hg =>
    simp only [_root_.map_add, LinearMap.add_apply, hf, hg]

/-- Full rational prime extraction commutes with the actual rational Hom map. -/
theorem rationalFullToPrime_homMap (f : Rationalization.Hom A B)
    (y : RationalFull A T) :
    rationalFullToPrime B T p (rationalHomMap T (fun _ => True) f y) =
      PrimeAdic.rationalHomMap T p f (rationalFullToPrime A T p y) :=
  rationalToPrime_homMap T (fun _ => True) p (fun _ => trivial) f y

/-- Actual full rational prime extraction on an abelian scheme is surjective. -/
theorem rationalFullToPrime_surjective (A : AbelianScheme S) :
    Function.Surjective (rationalFullToPrime A T p) :=
  GroupScheme.Tate.PrimeComparison.rationalFullToPrime_surjective A.toGrp T p

/-- Identity after prime extraction of every full section implies identity of the
actual prime Tate operator. -/
theorem rationalHomMap_eq_id_of_extraction_fixed (A : AbelianScheme S)
    (f : Rationalization.End A)
    (hf : ∀ y : RationalFull A T,
      rationalFullToPrime A T p (rationalHomMap T (fun _ => True) f y) =
        rationalFullToPrime A T p y) :
    PrimeAdic.rationalHomMap T p f = LinearMap.id := by
  ext x
  obtain ⟨y, rfl⟩ := rationalFullToPrime_surjective T p A x
  exact (rationalFullToPrime_homMap T p f y).symm.trans (hf y)

end Langlands.AbelianScheme.Tate.PrimeComparison
