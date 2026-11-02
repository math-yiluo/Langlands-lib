import Langlands.GroupScheme.FiniteEtaleImage
import Langlands.GroupScheme.Products
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-! # Finite sums of finite étale subgroup images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.FiniteEtale

instance coverProperty_isClosedUnderFiniteProducts (S : Scheme.{u}) :
    (coverProperty S).IsClosedUnderFiniteProducts := by
  let : HasFiniteLimits (Cover S) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesFiniteLimits (inclusion S) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks (inclusion S)
  let : (coverProperty S).IsClosedUnderIsomorphisms := {
    of_iso := fun {X Y} e hX => by
      have : IsFinite X.hom := hX.1
      have : Etale X.hom := hX.2
      have : IsIso e.inv.left :=
        inferInstanceAs (IsIso ((Over.forget S).map e.inv))
      change IsFinite Y.hom ∧ Etale Y.hom
      rw [← Over.w e.inv]
      exact ⟨inferInstance, inferInstance⟩ }
  exact ⟨fun J _ =>
    (coverProperty S).isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι (Discrete J)⟩

end Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.GroupScheme.FiniteEtaleSum

variable {S : Scheme.{u}} {I : Type u} [Fintype I] (G : I → GroupScheme S)

/-- The underlying scheme of a finite product is finite étale over the base. -/
theorem finiteEtale_pi [∀ i, IsFinite (G i).X.hom] [∀ i, Etale (G i).X.hom] :
    Langlands.AlgebraicGeometry.FiniteEtale.coverProperty S (GroupScheme.pi G).X :=
  (Langlands.AlgebraicGeometry.FiniteEtale.coverProperty S).prop_of_isLimit_fan
    (GroupScheme.piIsLimit G) (fun _ => ⟨inferInstance, inferInstance⟩)

instance [∀ i, IsFinite (G i).X.hom] [∀ i, Etale (G i).X.hom] :
    IsFinite (GroupScheme.pi G).X.hom := (finiteEtale_pi G).1
instance [∀ i, IsFinite (G i).X.hom] [∀ i, Etale (G i).X.hom] :
    Etale (GroupScheme.pi G).X.hom := (finiteEtale_pi G).2

variable {G} {H : GroupScheme S} [IsCommMonObj H.X]

/-- Sum a finite family of homomorphisms on separate product coordinates. -/
def sumMap (f : ∀ i, G i ⟶ H) : GroupScheme.pi G ⟶ H :=
  ∏ i, Pi.π G i ≫ f i

omit [Fintype I] in
private theorem comp_prod {P Q : GroupScheme S} (a : P ⟶ Q)
    (g : I → (Q ⟶ H)) (s : Finset I) :
    a ≫ ∏ i ∈ s, g i = ∏ i ∈ s, a ≫ g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | @insert i s hi ih => simp [hi, MonObj.comp_mul, ih]

variable [∀ i, IsCommMonObj (G i).X]

/-- Insert one coordinate, using the unit on all other coordinates. -/
def coordinate (i : I) : G i ⟶ GroupScheme.pi G := by
  classical
  exact Pi.lift (fun j => if h : i = j then eqToHom (congrArg G h) else 1)

@[reassoc (attr := simp)]
theorem coordinate_sumMap (f : ∀ i, G i ⟶ H) (i : I) :
    coordinate i ≫ sumMap f = f i := by
  classical
  rw [sumMap, comp_prod]
  calc
    _ = coordinate i ≫ Pi.π G i ≫ f i := by
      apply Finset.prod_eq_single i
      · intro j _ hji
        simp [coordinate, Ne.symm hji, MonObj.one_comp]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    _ = f i := by simp [coordinate]

variable [∀ i, IsFinite (G i).X.hom] [∀ i, Etale (G i).X.hom]
  [IsFinite H.X.hom] [Etale H.X.hom]

/-- The actual finite étale subgroup obtained by summing the family of images. -/
abbrev image (f : ∀ i, G i ⟶ H) : GroupScheme S :=
  FiniteEtaleImage.image (sumMap f)

/-- The actual closed inclusion of the sum subgroup. -/
abbrev inclusion (f : ∀ i, G i ⟶ H) : image f ⟶ H :=
  FiniteEtaleImage.inclusion (sumMap f)

/-- The finite étale surjection from the product onto the sum subgroup. -/
abbrev projection (f : ∀ i, G i ⟶ H) : GroupScheme.pi G ⟶ image f :=
  FiniteEtaleImage.projection (sumMap f)

/-- Each original homomorphism factors through the actual sum subgroup. -/
def component (f : ∀ i, G i ⟶ H) (i : I) : G i ⟶ image f :=
  coordinate i ≫ projection f

@[reassoc (attr := simp)]
theorem component_inclusion (f : ∀ i, G i ⟶ H) (i : I) :
    component f i ≫ inclusion f = f i := by
  rw [component, Category.assoc, FiniteEtaleImage.projection_inclusion, coordinate_sumMap]

/-- Killing the actual sum subgroup is equivalent to killing every summand. -/
theorem inclusion_comp_eq_one_iff (f : ∀ i, G i ⟶ H)
    {J : GroupScheme S} [IsCommMonObj J.X] (g : H ⟶ J) :
    inclusion f ≫ g = 1 ↔ ∀ i, f i ≫ g = 1 := by
  constructor
  · intro h i
    rw [← component_inclusion f i, Category.assoc, h, MonObj.comp_one]
  · intro h
    apply (FiniteEtaleImage.inclusion_comp_eq_one_iff (sumMap f) g).2
    change (IsMonHom.monoidHom g (GroupScheme.pi G)) (∏ i, Pi.π G i ≫ f i) = 1
    rw [map_prod]
    change (∏ i, (Pi.π G i ≫ f i) ≫ g) = 1
    simp [Category.assoc, h, MonObj.comp_one]

end Langlands.GroupScheme.FiniteEtaleSum
