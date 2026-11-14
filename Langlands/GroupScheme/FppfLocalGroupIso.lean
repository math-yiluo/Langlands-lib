import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Mathlib.AlgebraicGeometry.Morphisms.Descent

/-! # Descent of local group isomorphisms on fppf covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}

namespace LocalGroupHom

variable (e : LocalGroupHom G H U)

private theorem fppfUnderlyingRel {V Z Y : Over S} (p : V ⟶ Z) (f : V ⟶ Y)
    (hf : ∀ {W : Over S} (a b : W ⟶ V), a ≫ p = b ≫ p → a ≫ f = b ≫ f)
    {W : Scheme} (a b : W ⟶ V.left) (hab : a ≫ p.left = b ≫ p.left) :
    a ≫ f.left = b ≫ f.left := by
  have hb : b ≫ V.hom = a ≫ V.hom := by
    rw [← Over.w p, ← Category.assoc, ← Category.assoc, hab]
  let a₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk a rfl
  let b₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk b hb
  exact congrArg (fun q => q.left) (hf a₀ b₀ (Over.OverMorphism.ext hab))

private def fppfOverDesc {V Z Y : Over S} (p : V ⟶ Z) [EffectiveEpi p.left]
    (f : V ⟶ Y)
    (hf : ∀ {W : Over S} (a b : W ⟶ V), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    Z ⟶ Y := by
  let d : Z.left ⟶ Y.left := EffectiveEpi.desc p.left f.left (fppfUnderlyingRel p f hf)
  exact Over.homMk d (by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, show p.left ≫ d = f.left from EffectiveEpi.fac _ _ _,
      Over.w f, Over.w p])

private theorem fppfOverDesc_fac {V Z Y : Over S} (p : V ⟶ Z) [EffectiveEpi p.left]
    (f : V ⟶ Y)
    (hf : ∀ {W : Over S} (a b : W ⟶ V), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    p ≫ fppfOverDesc p f hf = f := by
  apply Over.OverMorphism.ext
  change p.left ≫ EffectiveEpi.desc p.left f.left (fppfUnderlyingRel p f hf) = f.left
  exact EffectiveEpi.fac p.left f.left (fppfUnderlyingRel p f hf)

variable [LocallyOfFinitePresentation U.hom] [Flat U.hom] [Surjective U.hom]

private instance fppfEffectiveEpi_fst (Z : Over S) : EffectiveEpi (fst Z U).left := by
  change EffectiveEpi (CategoryTheory.Limits.pullback.fst Z.hom U.hom)
  infer_instance

variable (he : e.IsIndependent)

include he

omit [LocallyOfFinitePresentation U.hom] [Flat U.hom] [Surjective U.hom] in
private theorem fppfLocalRel (Z : Over S) (g : Z ⟶ G.X)
    {W : Over S} (a b : W ⟶ Z ⊗ U) (hab : a ≫ fst Z U = b ≫ fst Z U) :
    a ≫ e.toFun (snd Z U) (fst Z U ≫ g) =
      b ≫ e.toFun (snd Z U) (fst Z U ≫ g) := by
  rw [← e.naturality, ← e.naturality]
  simp only [← Category.assoc, hab]
  exact he _ _ _

/-- Descend the value of an independent local homomorphism at a group point. -/
def valueFppf {Z : Over S} (g : Z ⟶ G.X) : Z ⟶ H.X :=
  fppfOverDesc (fst Z U) (e.toFun (snd Z U) (fst Z U ≫ g)) (e.fppfLocalRel he Z g)

theorem valueFppf_fac {Z : Over S} (g : Z ⟶ G.X) :
    fst Z U ≫ e.valueFppf he g = e.toFun (snd Z U) (fst Z U ≫ g) :=
  fppfOverDesc_fac (fst Z U) (e.toFun (snd Z U) (fst Z U ≫ g)) (e.fppfLocalRel he Z g)

/-- Pulling a descended point to any test with a cover point recovers its local value. -/
theorem comp_valueFppf {Z W : Over S} (t : W ⟶ Z) (a : W ⟶ U) (g : Z ⟶ G.X) :
    t ≫ e.valueFppf he g = e.toFun a (t ≫ g) := by
  have h := congrArg (fun q => lift t a ≫ q) (e.valueFppf_fac he g)
  simpa only [← Category.assoc, lift_fst, ← e.naturality, lift_snd] using h

theorem valueFppf_naturality {Z W : Over S} (t : W ⟶ Z) (g : Z ⟶ G.X) :
    e.valueFppf he (t ≫ g) = t ≫ e.valueFppf he g := by
  apply Over.OverMorphism.ext
  apply (cancel_epi (fst W U).left).mp
  have h : fst W U ≫ e.valueFppf he (t ≫ g) = fst W U ≫ (t ≫ e.valueFppf he g) := by
    calc
      _ = e.toFun (snd W U) (fst W U ≫ (t ≫ g)) := e.valueFppf_fac he (t ≫ g)
      _ = e.toFun (snd W U) ((fst W U ≫ t) ≫ g) := by rw [Category.assoc]
      _ = (fst W U ≫ t) ≫ e.valueFppf he g :=
        (e.comp_valueFppf he (fst W U ≫ t) (snd W U) g).symm
      _ = _ := Category.assoc _ _ _
  exact congrArg (fun q => q.left) h

/-- The descended values preserve multiplication. -/
def pointsHomFppf (Z : Over S) : (Z ⟶ G.X) →* (Z ⟶ H.X) where
  toFun := e.valueFppf he
  map_one' := by
    apply Over.OverMorphism.ext
    apply (cancel_epi (fst Z U).left).mp
    have h : fst Z U ≫ e.valueFppf he (1 : Z ⟶ G.X) = fst Z U ≫ (1 : Z ⟶ H.X) := by
      rw [e.valueFppf_fac, MonObj.comp_one, map_one, MonObj.comp_one]
    exact congrArg (fun q => q.left) h
  map_mul' g g' := by
    apply Over.OverMorphism.ext
    apply (cancel_epi (fst Z U).left).mp
    have h : fst Z U ≫ e.valueFppf he (g * g') =
        fst Z U ≫ (e.valueFppf he g * e.valueFppf he g') := by
      rw [e.valueFppf_fac, MonObj.comp_mul, map_mul, MonObj.comp_mul,
        e.valueFppf_fac, e.valueFppf_fac]
    exact congrArg (fun q => q.left) h

/-- An independent natural family descends to an actual group-scheme homomorphism. -/
def descendFppf : G ⟶ H :=
  homOfPoints (e.pointsHomFppf he) (e.valueFppf_naturality he)

@[simp] theorem comp_descendFppf (Z : Over S) (g : Z ⟶ G.X) :
    g ≫ (e.descendFppf he).hom.hom = e.valueFppf he g :=
  comp_homOfPoints (e.pointsHomFppf he) (e.valueFppf_naturality he) Z g

end LocalGroupHom

namespace LocalGroupIso

variable (e : LocalGroupIso G H U)

variable [LocallyOfFinitePresentation U.hom] [Flat U.hom] [Surjective U.hom]

private theorem descendFppf_comp_symm (he : e.IsIndependent) :
    e.toLocalGroupHom.descendFppf he ≫
      e.symm.toLocalGroupHom.descendFppf (IsIndependent.symm e he) = 𝟙 G := by
  apply hom_ext_points
  intro Z g
  change g ≫ ((e.toLocalGroupHom.descendFppf he).hom.hom ≫
      (e.symm.toLocalGroupHom.descendFppf (IsIndependent.symm e he)).hom.hom) = g
  rw [← Category.assoc]
  rw [LocalGroupHom.comp_descendFppf e.symm.toLocalGroupHom (IsIndependent.symm e he),
    LocalGroupHom.comp_descendFppf e.toLocalGroupHom he]
  apply Over.OverMorphism.ext
  have : EffectiveEpi (fst Z U).left := by
    change EffectiveEpi (CategoryTheory.Limits.pullback.fst Z.hom U.hom)
    infer_instance
  apply (cancel_epi (fst Z U).left).mp
  have h : fst Z U ≫ e.symm.toLocalGroupHom.valueFppf (IsIndependent.symm e he)
      (e.toLocalGroupHom.valueFppf he g) = fst Z U ≫ g := by
    calc
      _ = (e.toFun (snd Z U)).symm (fst Z U ≫ e.toLocalGroupHom.valueFppf he g) :=
        e.symm.toLocalGroupHom.valueFppf_fac (IsIndependent.symm e he) _
      _ = (e.toFun (snd Z U)).symm (e.toFun (snd Z U) (fst Z U ≫ g)) :=
        congrArg (e.toFun (snd Z U)).symm (e.toLocalGroupHom.valueFppf_fac he g)
      _ = _ := MulEquiv.symm_apply_apply (e.toFun (snd Z U)) _
  exact congrArg (fun q => q.left) h

/-- An independent local isomorphism descends to a genuine group-scheme isomorphism. -/
def descendFppf (he : e.IsIndependent) : G ≅ H where
  hom := e.toLocalGroupHom.descendFppf he
  inv := e.symm.toLocalGroupHom.descendFppf (IsIndependent.symm e he)
  hom_inv_id := e.descendFppf_comp_symm he
  inv_hom_id := e.symm.descendFppf_comp_symm (IsIndependent.symm e he)

/-- Triviality of an actual discrepancy cocycle descends the local group isomorphism. -/
def descendOfTrivialFppf (a : AutomorphicAction A G) (ξ : Cocycle A U)
    (h : e.HasDiscrepancy a ξ) (hξ : ξ.IsTrivial) : G ≅ H :=
  (e.twist a hξ.choose).descendFppf (e.twist_isIndependent a ξ h hξ.choose hξ.choose_spec)

/-- Triviality of the natural cocycle constructed from innerness descends the local
isomorphism on an fppf cover. -/
def descendOfTrivialInnerCocycleFppf (a : AutomorphicAction A G)
    (ha : a.IsFaithful) (he : e.HasInnerDiscrepancy a)
    (hξ : (e.innerCocycle a ha he).IsTrivial) : G ≅ H :=
  e.descendOfTrivialFppf a (e.innerCocycle a ha he)
    (e.innerCocycle_hasDiscrepancy a ha he) hξ

end LocalGroupIso

end Langlands.GroupScheme
