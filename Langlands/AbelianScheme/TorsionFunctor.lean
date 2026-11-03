import Langlands.AbelianScheme.TorsionBaseChange
import Langlands.AbelianScheme.GroupScheme
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Functoriality of actual integer torsion group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H J : Grp (Over S)}
  [IsCommMonObj G.X] [IsCommMonObj H.X] [IsCommMonObj J.X]

/-- Restrict an actual homomorphism to its integer torsion subgroup schemes. -/
def torsionMap (f : G ⟶ H) (n : ℤ) : torsion G n ⟶ torsion H n :=
  pullback.map (multiplication G n) (kernelUnit G)
    (multiplication H n) (kernelUnit H) f (𝟙 _) f
    (multiplication_naturality f n) (by
      apply Grp.hom_ext
      change η[G.X] ≫ f.hom.hom = 𝟙 _ ≫ η[H.X]
      rw [Category.id_comp, IsMonHom.one_hom])

@[reassoc (attr := simp)]
theorem torsionMap_ι (f : G ⟶ H) (n : ℤ) :
    torsionMap f n ≫ torsionι H n = torsionι G n ≫ f :=
  pullback.lift_fst _ _ _

/-- Equality of homomorphisms into torsion can be tested after its inclusion. -/
theorem torsion_hom_ext (n : ℤ) {P : Grp (Over S)}
    (a b : P ⟶ torsion H n) (h : a ≫ torsionι H n = b ≫ torsionι H n) : a = b := by
  apply Grp.hom_ext
  apply (cancel_mono (torsionι H n).hom.hom).mp
  exact congrArg (fun k => k.hom.hom) h

@[simp]
theorem torsionMap_id (n : ℤ) : torsionMap (𝟙 G) n = 𝟙 (torsion G n) := by
  apply torsion_hom_ext n
  simp

@[simp]
theorem torsionMap_comp (f : G ⟶ H) (g : H ⟶ J) (n : ℤ) :
    torsionMap (f ≫ g) n = torsionMap f n ≫ torsionMap g n := by
  apply torsion_hom_ext n
  simp [Category.assoc]

@[simp]
theorem torsionMap_one (n : ℤ) : torsionMap (1 : G ⟶ H) n = 1 := by
  apply torsion_hom_ext n
  simp [MonObj.comp_one, MonObj.one_comp]

@[simp]
theorem torsionMap_mul (f g : G ⟶ H) (n : ℤ) :
    torsionMap (f * g) n = torsionMap f n * torsionMap g n := by
  apply torsion_hom_ext n
  simp [MonObj.comp_mul, MonObj.mul_comp]

/-- The restriction is a homomorphism for the pointwise Hom group laws. -/
def torsionMapHom (n : ℤ) : (G ⟶ H) →* (torsion G n ⟶ torsion H n) where
  toFun f := torsionMap f n
  map_one' := torsionMap_one n
  map_mul' f g := torsionMap_mul f g n

/-- The actual torsion inclusion is killed by multiplication by its defining integer. -/
@[simp]
theorem torsionι_multiplication (n : ℤ) :
    torsionι G n ≫ multiplication G n = 1 := by
  apply Grp.hom_ext
  exact (kernel_isPullback (multiplication G n)).w

/-- Multiplication by the defining integer is trivial on the torsion scheme itself. -/
@[simp]
theorem multiplication_torsion (n : ℤ) : multiplication (torsion G n) n = 1 := by
  apply torsion_hom_ext n
  rw [multiplication_naturality, torsionι_multiplication, MonObj.one_comp]

/-- Restriction agrees with postcomposition on every test scheme's actual torsion points. -/
theorem torsionPointsEquiv_map (f : G ⟶ H) (n : ℤ) (T : Over S)
    (x : T ⟶ (torsion G n).X) :
    (torsionPointsEquiv H n T (x ≫ (torsionMap f n).hom.hom)).val =
      (torsionPointsEquiv G n T x).val ≫ f.hom.hom := by
  change (x ≫ (torsionMap f n).hom.hom) ≫ (torsionι H n).hom.hom = _
  rw [Category.assoc]
  exact congrArg (fun k => x ≫ k.hom.hom) (torsionMap_ι f n)

/-- Restriction to integer torsion commutes with arbitrary scheme base change. -/
theorem torsionMap_baseChange {S' : Scheme.{u}} (b : S' ⟶ S) (f : G ⟶ H) (n : ℤ) :
    (Over.pullback b).mapGrp.map (torsionMap f n) ≫
        (torsionBaseChangeIso b H n).hom =
      (torsionBaseChangeIso b G n).hom ≫
        torsionMap ((Over.pullback b).mapGrp.map f) n := by
  apply torsion_hom_ext n
  simp only [Category.assoc, torsionBaseChangeIso_hom_ι, torsionMap_ι,
    ← Functor.map_comp, torsionBaseChangeIso_hom_ι_assoc]

end Langlands.GroupScheme

namespace Langlands.CommGroupScheme

variable {S : Scheme.{u}}

/-- The actual integer torsion construction as a functor in additive notation. -/
def torsionFunctor (n : ℤ) : CommGroupScheme S ⥤ CommGroupScheme S where
  obj G := { toGrp := GroupScheme.torsion G.toGrp n }
  map f := Additive.ofMul (GroupScheme.torsionMap (groupHom f) n)
  map_id G := congrArg Additive.ofMul (GroupScheme.torsionMap_id (G := G.toGrp) n)
  map_comp f g := congrArg Additive.ofMul
    (GroupScheme.torsionMap_comp (groupHom f) (groupHom g) n)

instance (n : ℤ) : (torsionFunctor (S := S) n).Additive where
  map_add := congrArg Additive.ofMul (GroupScheme.torsionMap_mul _ _ n)

/-- The torsion subgroup inclusions are natural actual group-scheme homomorphisms. -/
def torsionInclusion (n : ℤ) : torsionFunctor (S := S) n ⟶ 𝟭 (CommGroupScheme S) where
  app G := Additive.ofMul (GroupScheme.torsionι G.toGrp n)
  naturality := by
    intro G H f
    exact congrArg Additive.ofMul (GroupScheme.torsionMap_ι (groupHom f) n)

end Langlands.CommGroupScheme
