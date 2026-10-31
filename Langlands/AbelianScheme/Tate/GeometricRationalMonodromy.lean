import Langlands.AbelianScheme.Tate.RationalTopology
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.RepresentationTheory.Rep.Basic

/-! # The actual geometric rational Tate representation functor -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AbelianScheme.Tate.Geometric

universe u
open Langlands.AlgebraicGeometry
open GroupScheme.Tate (Index)

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

local notation "Γs" => FiniteEtale.FundamentalGroup s (FiniteEtale.geometricFiberFinite s)

variable (A : AbelianScheme S) (P : ℕ → Prop)
  (hunit : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤)))

/-- The actual rational Tate action, using proved geometric finiteness and finite etaleness. -/
def rationalRepresentation : Representation ℚ Γs (Rational A (Over.mk s) P) where
  toFun := rationalMonodromyMap s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit
  map_one' := LinearMap.ext (rationalMonodromyMap_one s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit)
  map_mul' g h := LinearMap.ext (rationalMonodromyMap_mul s
    (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit g h)

@[simp] theorem rationalRepresentation_tmul (g : Γs) (q : ℚ)
    (x : Integral A (Over.mk s) P) :
    rationalRepresentation s A P hunit g (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] integralMonodromy s
        (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit g x := rfl

/-- Rationalization intertwines the actual integral and rational geometric actions. -/
theorem rationalRepresentation_toRational (g : Γs) (x : Integral A (Over.mk s) P) :
    rationalRepresentation s A P hunit g (GroupScheme.Tate.toRational A.toGrp (Over.mk s) P x) =
      GroupScheme.Tate.toRational A.toGrp (Over.mk s) P
        (integralMonodromy s
          (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale A P hunit g x) := rfl

/-- Bundle the existing rational Tate carrier with its actual geometric action. -/
def rationalRep : Rep ℚ Γs := Rep.of (rationalRepresentation s A P hunit)

variable {A} {B : AbelianScheme S}

/-- Existing rational homomorphism maps, now bundled as actual intertwining maps. -/
def rationalRepMap (f : Rationalization.Hom A B) :
    rationalRep s A P hunit ⟶ rationalRep s B P hunit :=
  Rep.ofHom {
    toLinearMap := rationalHomMap (Over.mk s) P f
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact (rationalMonodromy_homMap s
        (FiniteEtale.geometricFiberFinite s) torsionFiniteEtale P hunit f g x).symm }

@[simp] theorem rationalRepMap_toLinearMap (f : Rationalization.Hom A B) :
    (rationalRepMap s P hunit f).hom.toLinearMap = rationalHomMap (Over.mk s) P f := rfl

/-- The geometric rational Tate functor on the actual rationalized category. -/
def rationalRepFunctor : Rationalization (AbelianScheme S) ⥤ Rep ℚ Γs where
  obj A := rationalRep s A.obj P hunit
  map f := rationalRepMap s P hunit f
  map_id A := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact rationalHomMap_identity (Over.mk s) P
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact rationalHomMap_comp (Over.mk s) P f g

instance : (rationalRepFunctor s P hunit).Additive where
  map_add {_ _ f g} := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact (rationalHomMap (Over.mk s) P).map_add f g

instance : (rationalRepFunctor s P hunit).Linear ℚ where
  map_smul f q := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact (rationalHomMap (Over.mk s) P).map_smul q f

/-- Forgetting monodromy recovers the already published rationalized Tate functor. -/
def rationalRepForgetIso :
    rationalRepFunctor s P hunit ⋙ forget₂ (Rep ℚ Γs) (ModuleCat ℚ) ≅
      rationalizedFunctor (Over.mk s) P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply ModuleCat.hom_ext
    rfl)

@[simp] theorem rationalRepFunctor_map_ofHom (f : A ⟶ B) (x : Rational A (Over.mk s) P) :
    ((rationalRepFunctor s P hunit).map (Rationalization.ofHom f)).hom.toLinearMap x =
      rationalMap (Over.mk s) P f x :=
  LinearMap.congr_fun (rationalHomMap_ofHom (Over.mk s) P f) x

@[simp] theorem rationalRepFunctor_map_tmul (q : ℚ) (f : A ⟶ B)
    (x : Rational A (Over.mk s) P) :
    ((rationalRepFunctor s P hunit).map (q ⊗ₜ[ℤ] f)).hom.toLinearMap x =
      q • rationalMap (Over.mk s) P f x := rfl

/-- Rational isomorphisms induce the same linear equivalences as the existing Tate functor. -/
theorem rationalRepFunctor_mapIso (e : Rationalization.of A ≅ Rationalization.of B)
    (x : Rational A (Over.mk s) P) :
    ((rationalRepFunctor s P hunit).mapIso e).hom.hom.toLinearMap x =
      rationalIso (Over.mk s) P e x := rfl

end Langlands.AbelianScheme.Tate.Geometric
