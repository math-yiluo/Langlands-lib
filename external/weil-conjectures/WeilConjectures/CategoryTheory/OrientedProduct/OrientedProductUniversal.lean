/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Sheaf.SheafSubcategoryComparison
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The oriented product of topoi

Source: ILO, Exposé XI §§1.1–1.7, printed pp. 171–174
(blueprint: lem-trf-oriented-product-universal).

The comma category is the actual category of triples. The precoverage includes the
isomorphic versions of the three displayed generators, which generate the same topology.
-/

@[expose] public section

universe u e ve x y s p z vx vy vs vp vz

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OrientedProduct

variable {C₁ C₂ D : Type u} [SmallCategory C₁] [SmallCategory C₂] [SmallCategory D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]

/-- The category of triples, using Mathlib's comma and product categories.
Source: ILO XI §1.1(i) (blueprint: lem-trf-oriented-product-universal). -/
abbrev Triples (F : D ⥤ C₁) (G : D ⥤ C₂) := Comma (𝟭 (C₁ × C₂)) (F.prod' G)

/-- The three generating covering types. Unchanged components are allowed to be isomorphisms;
this is the isomorphism closure of the literal generators in XI §1.1(ii)(a)–(c).
Source: ILO XI §1.1(ii) (blueprint: lem-trf-oriented-product-universal). -/
def generators (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : Precoverage (Triples F G) where
  coverings Z := {R |
    (∃ (I : Type u) (Zᵢ : I → Triples F G) (r : ∀ i, Zᵢ i ⟶ Z),
      R = Presieve.ofArrows Zᵢ r ∧
      ((Presieve.ofArrows (fun i ↦ (Zᵢ i).left.1) (fun i ↦ (r i).left.1) ∈ J₁ Z.left.1 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.2) ∨
       (Presieve.ofArrows (fun i ↦ (Zᵢ i).left.2) (fun i ↦ (r i).left.2) ∈ J₂ Z.left.2 ∧
        ∀ i, IsIso (r i).right ∧ IsIso (r i).left.1))) ∨
    (∃ (Z' : Triples F G) (r : Z' ⟶ Z), R = Presieve.singleton r ∧
      IsIso r.left.1 ∧ IsPullback r.left.2 Z'.hom.2 Z.hom.2 (G.map r.right))}

/-- The generated Grothendieck topology, with no unproved data.
Source: ILO XI §1.1(ii) (blueprint: lem-trf-oriented-product-universal). -/
def topology (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (F : D ⥤ C₁) (G : D ⥤ C₂) : GrothendieckTopology (Triples F G) :=
  (generators J₁ J₂ F G).toGrothendieck

/-- Associated representables, including on sites that are not subcanonical.
Source: ILO XI §§1.2–1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def associated {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    C ⥤ Sheaf J (Type u) := yoneda ⋙ presheafToSheaf J (Type u)

/-- The first site projection on objects, using final objects.
Source: ILO XI §1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def firstTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (U : C₁) : Triples F G where
  left := (U, ⊤_ C₂)
  right := ⊤_ D
  hom := (terminal.from U ≫ inv (terminalComparison F), inv (terminalComparison G))

/-- The second site projection on objects.
Source: ILO XI §1.3 (blueprint: lem-trf-oriented-product-universal). -/
noncomputable def secondTriple (F : D ⥤ C₁) (G : D ⥤ C₂)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (W : C₂) : Triples F G where
  left := (⊤_ C₁, W)
  right := ⊤_ D
  hom := (inv (terminalComparison F), terminal.from W ≫ inv (terminalComparison G))

variable (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- The first projection site functor. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def first : C₁ ⥤ Triples F G where
  obj := firstTriple F G
  map r := ⟨(r, 𝟙 _), 𝟙 _, by
    apply Prod.ext <;> simp [firstTriple]⟩
  map_comp _ _ := by ext <;> simp [firstTriple]

/-- The second projection site functor. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def second : C₂ ⥤ Triples F G where
  obj := secondTriple F G
  map r := ⟨(𝟙 _, r), 𝟙 _, by
    apply Prod.ext <;> simp [secondTriple]⟩
  map_comp _ _ := by ext <;> simp [secondTriple]

/-- Structural arrow to the first projection triple. Source: ILO XI Lemma 1.5
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def toFirst (Z : Triples F G) : Z ⟶ (first F G).obj Z.left.1 where
  left := (𝟙 _, terminal.from _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- Structural arrow to the second projection triple. Source: ILO XI Lemma 1.5
(blueprint: lem-trf-oriented-product-universal). -/
noncomputable def toSecond (Z : Triples F G) : Z ⟶ (second F G).obj Z.left.2 where
  left := (terminal.from _, 𝟙 _)
  right := terminal.from _
  w := Prod.ext
    ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
    ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _)

/-- The middle triple defining the orientation. Source: ILO XI §1.3
(blueprint: lem-trf-oriented-product-universal). -/
def middle (V : D) : Triples F G := ⟨(F.obj V, G.obj V), V, (𝟙 _, 𝟙 _)⟩

/-- Transport a cone's 2-morphism along its two projection isomorphisms.
Source: ILO XI Theorem 1.4 (blueprint: lem-trf-oriented-product-universal). -/
def paste {X : Type x} {Y : Type y} {S : Type s} {P : Type p} {E : Type z}
    [Category.{vx} X] [Category.{vy} Y] [Category.{vs} S]
    [Category.{vp} P] [Category.{vz} E]
    (f : GeometricMorphism X S) (g : GeometricMorphism Y S)
    (p₁ : GeometricMorphism P X) (p₂ : GeometricMorphism P Y)
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct)
    (h : GeometricMorphism E P) (a : GeometricMorphism E X)
    (b : GeometricMorphism E Y)
    (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct) :
    (b.comp g).direct ⟶ (a.comp f).direct :=
  (Functor.isoWhiskerRight β.symm g.direct).hom ≫
    (Functor.associator h.direct p₂.direct g.direct).hom ≫
    Functor.whiskerLeft h.direct τ ≫
    (Functor.associator h.direct p₁.direct f.direct).inv ≫
    (Functor.isoWhiskerRight α f.direct).hom

/-- The universal compatible lift, including uniqueness of its isomorphism.
All topoi of the indicated universes are tested, without a choice of presentation.
Source: ILO XI Theorem 1.4 (blueprint: lem-trf-oriented-product-universal). -/
def IsUniversal {X Y S P : Type (u + 1)} [Category.{u} X] [Category.{u} Y]
    [Category.{u} S] [Category.{u} P]
    (f : GeometricMorphism X S) (g : GeometricMorphism Y S)
    (p₁ : GeometricMorphism P X) (p₂ : GeometricMorphism P Y)
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct) : Prop :=
  ∀ (E : Type e) [Category.{ve} E], IsGrothendieckTopos.{u} E →
    ∀ (a : GeometricMorphism E X) (b : GeometricMorphism E Y)
      (t : (b.comp g).direct ⟶ (a.comp f).direct),
    ∃ (h : GeometricMorphism E P)
      (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct),
      paste f g p₁ p₂ τ h a b α β = t ∧
      ∀ (h' : GeometricMorphism E P)
        (α' : (h'.comp p₁).direct ≅ a.direct) (β' : (h'.comp p₂).direct ≅ b.direct),
        paste f g p₁ p₂ τ h' a b α' β' = t →
        ∃! γ : h.direct ≅ h'.direct,
          Functor.isoWhiskerRight γ p₁.direct ≪≫ α' = α ∧
          Functor.isoWhiskerRight γ p₂.direct ≪≫ β' = β

/-- The defining pullback formula, with its actual structural maps; it is required for
all compatible lifts, hence in particular for the universal lift.
Source: ILO XI §1.6, formula (1.a) (blueprint: lem-trf-oriented-product-universal). -/
def HasLiftFormula (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type u))
      (Sheaf K.toGrothendieck (Type u)))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type u))
      (Sheaf K.toGrothendieck (Type u)))
    (ηF : associated K.toGrothendieck ⋙ f.inverse ≅ F ⋙ associated J₁.toGrothendieck)
    (ηG : associated K.toGrothendieck ⋙ g.inverse ≅ G ⋙ associated J₂.toGrothendieck)
    (p₁ : GeometricMorphism (Sheaf (topology J₁ J₂ F G) (Type u))
      (Sheaf J₁.toGrothendieck (Type u)))
    (p₂ : GeometricMorphism (Sheaf (topology J₁ J₂ F G) (Type u))
      (Sheaf J₂.toGrothendieck (Type u)))
    (π₁ : associated J₁.toGrothendieck ⋙ p₁.inverse ≅
      first F G ⋙ associated (topology J₁ J₂ F G))
    (π₂ : associated J₂.toGrothendieck ⋙ p₂.inverse ≅
      second F G ⋙ associated (topology J₁ J₂ F G))
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct) : Prop :=
  ∀ (E : Type e) [Category.{ve} E], IsGrothendieckTopos.{u} E →
    ∀ (a : GeometricMorphism E (Sheaf J₁.toGrothendieck (Type u)))
      (b : GeometricMorphism E (Sheaf J₂.toGrothendieck (Type u)))
      (t : (b.comp g).direct ⟶ (a.comp f).direct)
      (h : GeometricMorphism E (Sheaf (topology J₁ J₂ F G) (Type u)))
      (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct),
      paste f g p₁ p₂ τ h a b α β = t → ∀ Z : Triples F G,
      IsPullback
        (h.inverse.map ((associated (topology J₁ J₂ F G)).map (toFirst F G Z) ≫
            π₁.inv.app Z.left.1) ≫ (GeometricMorphism.inverseIso α).inv.app
              ((associated J₁.toGrothendieck).obj Z.left.1))
        (h.inverse.map ((associated (topology J₁ J₂ F G)).map (toSecond F G Z) ≫
            π₂.inv.app Z.left.2) ≫ (GeometricMorphism.inverseIso β).inv.app
              ((associated J₂.toGrothendieck).obj Z.left.2))
        (a.inverse.map ((associated J₁.toGrothendieck).map Z.hom.1 ≫ ηF.inv.app Z.right) ≫
          (GeometricMorphism.inverseMate t).app ((associated K.toGrothendieck).obj Z.right))
        (b.inverse.map ((associated J₂.toGrothendieck).map Z.hom.2 ≫ ηG.inv.app Z.right))

/-- The triple-site construction has its stated projections, canonical orientation,
universal compatible lift, and inverse-image pullback formula.

Source: ILO Exposé XI §§1.1, 1.3, Theorem 1.4, §1.6 formula (1.a), and Definition 1.7
(blueprint: lem-trf-oriented-product-universal).

Proof plan (the ten steps of the DAG node):
1. Form the comma category of triples. Finite limits are componentwise. The generators
are stable under base change; their saturation defines the topology, using
lem-weil-pbc-pretopology-sheaf-condition.
2. Descent for the first two types is ordinary descent. A type-(c) map has covering
 diagonal, so restriction is bijective. Yoneda and the sheafification adjunction
(def-weil-pbc-sheafification, lem-galois-yoneda-hom-bijection) make its associated map invertible.
3. The functors first and second preserve finite limits and covers. Apply
lem-weil-pbc-left-exact-site-inverse-image-tensor; adjunction and Yoneda identify their
inverse images on associated representables with the two projection formulas.
4. At V use the inverse of the type-(c) map from middle V to first (F V), followed by
its map to second (G V). Taking mates defines the displayed orientation.
5. Compute the componentwise pullbacks in XI Lemma 1.5. Yoneda and
situation-conventions preserve them. Cancel the type-(c) isomorphisms.
6. For a cone (a,b,t) form H(Z) by the displayed pullback. Naturality gives its action
on arrows. Finite limits commute with pullbacks by
lem-weil-pbc-site-sheaf-sets-limits-sectionwise, so H preserves finite limits.
7. The first two covering types map to pullbacks of epimorphic families; inverse images
preserve them using lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer, and their
pullbacks remain epimorphic by lem-weil-pbc-site-sheaf-sets-epi-locally-surjective.
The third type maps to an isomorphism by naturality of the inverse-image mate of t.
8. Enlarge generators of a presentation of E by the H(Z) and finite limits. Apply
lem-weil-pbc-site-of-sheaf-generators, then the left exact site inverse image theorem.
9. Evaluation on first and second gives alpha and beta. On middle V the inverse of
the first pullback projection followed by the second is exactly the mate of t.
Colimits of associated representables extend this equality to all sheaves.
10. Any other compatible lift preserves the pullback of step 5, forcing its inverse
image and its maps. Adjunction and Yoneda determine its direct image and the unique
projection-compatible isomorphism. Applying this to two site presentations gives
inverse equivalences, unique with projection and orientation compatibilities, which
is the site independence asserted in Definition 1.7.
-/
theorem universal (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    [F.IsContinuous K.toGrothendieck J₁.toGrothendieck]
    [G.IsContinuous K.toGrothendieck J₂.toGrothendieck]
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type u))
      (Sheaf K.toGrothendieck (Type u)))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type u))
      (Sheaf K.toGrothendieck (Type u)))
    (ηF : associated K.toGrothendieck ⋙ f.inverse ≅ F ⋙ associated J₁.toGrothendieck)
    (ηG : associated K.toGrothendieck ⋙ g.inverse ≅ G ⋙ associated J₂.toGrothendieck) :
    ∃ (p₁ : GeometricMorphism (Sheaf (topology J₁ J₂ F G) (Type u))
        (Sheaf J₁.toGrothendieck (Type u)))
      (p₂ : GeometricMorphism (Sheaf (topology J₁ J₂ F G) (Type u))
        (Sheaf J₂.toGrothendieck (Type u)))
      (π₁ : associated J₁.toGrothendieck ⋙ p₁.inverse ≅
        first F G ⋙ associated (topology J₁ J₂ F G))
      (π₂ : associated J₂.toGrothendieck ⋙ p₂.inverse ≅
        second F G ⋙ associated (topology J₁ J₂ F G))
      (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct),
      IsUniversal.{u, e, ve} f g p₁ p₂ τ ∧
      HasLiftFormula.{u, e, ve} F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ ∧
      (∀ (Q : Type (u + 1)) [Category.{u} Q], IsGrothendieckTopos.{u} Q →
        ∀ (q₁ : GeometricMorphism Q (Sheaf J₁.toGrothendieck (Type u)))
          (q₂ : GeometricMorphism Q (Sheaf J₂.toGrothendieck (Type u)))
          (σ : (q₂.comp g).direct ⟶ (q₁.comp f).direct),
          IsUniversal.{u, u + 1, u} f g q₁ q₂ σ →
          ∃ (h : GeometricMorphism Q (Sheaf (topology J₁ J₂ F G) (Type u)))
            (α : (h.comp p₁).direct ≅ q₁.direct) (β : (h.comp p₂).direct ≅ q₂.direct),
            paste f g p₁ p₂ τ h q₁ q₂ α β = σ ∧ h.direct.IsEquivalence ∧
            ∀ (h' : GeometricMorphism Q (Sheaf (topology J₁ J₂ F G) (Type u)))
              (α' : (h'.comp p₁).direct ≅ q₁.direct)
              (β' : (h'.comp p₂).direct ≅ q₂.direct),
              paste f g p₁ p₂ τ h' q₁ q₂ α' β' = σ →
              ∃! γ : h.direct ≅ h'.direct,
                Functor.isoWhiskerRight γ p₁.direct ≪≫ α' = α ∧
                Functor.isoWhiskerRight γ p₂.direct ≪≫ β' = β) ∧
      ∀ V : D,
        ∃ (_ : IsIso ((associated (topology J₁ J₂ F G)).map
          (toFirst F G (middle F G V)))),
        (GeometricMorphism.inverseMate τ).app ((associated K.toGrothendieck).obj V) =
          p₁.inverse.map (ηF.hom.app V) ≫ π₁.hom.app (F.obj V) ≫
          inv ((associated (topology J₁ J₂ F G)).map (toFirst F G (middle F G V))) ≫
          (associated (topology J₁ J₂ F G)).map (toSecond F G (middle F G V)) ≫
          π₂.inv.app (G.obj V) ≫ p₂.inverse.map (ηG.inv.app V) := by
  sorry

end CategoryTheory.OrientedProduct
