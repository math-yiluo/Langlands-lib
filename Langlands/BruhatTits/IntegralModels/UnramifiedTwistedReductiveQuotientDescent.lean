import Langlands.GroupScheme.IntegralModel.FiniteInnerUnramifiedRecovery
import Langlands.GroupScheme.IntegralModel.FiniteInnerInertiaSemilinearity
import Langlands.GroupScheme.IntegralModel.CommonFiniteInnerRecovery
import Langlands.GroupScheme.IntegralModel.InnerSemilinearExtension
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.Rational.ConjugateSection
import Langlands.GroupScheme.Torus.FrobeniusConjugate
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof
import Langlands.Galois.Local.SeparableHenselian
import Langlands.GroupScheme.IntegralModel.HenselianReduction
import Langlands.Geometry.Building.UnramifiedRecoveredFacetMaps
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.PerfectFieldProof
import Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalProof
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedTwistedReductiveQuotientDescentStatement

/-! # Frobenius descent of the reductive quotient of a twisted-stable unramified model

Proof of `UnramifiedTwistedReductiveQuotientDescentStatement`.  The neutral model is
descended along the inner twist to a smooth model `M` over `𝒪[F]`.  The group `R` is the
quotient of the special fibre of `M` by its unipotent radical, and the comparison with
`Q.quotient` comes from the uniqueness of fppf quotients.  The helper lemmas in
`TwistedResidueFrobenius` keep all objects as variables, so that the kernel checks their
instances by argument matching. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

namespace TwistedResidueFrobenius

section General

variable {S S' : Scheme.{u}}

/-- Sections of a base change are determined by their projection to the
original scheme. -/
theorem baseChange_section_ext (b : S' ⟶ S) (G : GroupScheme S)
    {x y : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X}
    (h : x.left ≫ pullback.fst G.X.hom b = y.left ≫ pullback.fst G.X.hom b) :
    x = y := by
  apply (baseChangeBasePointsEquiv b G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, baseChangeBasePointsEquiv_left]
  exact h

/-- Projection of the image of a section under a base-changed homomorphism. -/
theorem baseChange_map_fst (b : S' ⟶ S) {G H : GroupScheme S} (f : G ⟶ H)
    (x : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) :
    (x ≫ ((GroupScheme.baseChange b).map f).hom.hom).left ≫ pullback.fst H.X.hom b =
      x.left ≫ pullback.fst G.X.hom b ≫ f.hom.hom.left := by
  have h := congrArg (fun z => z.left) (baseChangeBasePointsEquiv_comp b f x)
  simp only [baseChangeBasePointsEquiv_left, Over.comp_left] at h
  simpa only [Over.comp_left, Category.assoc] using h

/-- A section of a base change lies over the base morphism. -/
theorem section_fst_hom (b : S' ⟶ S) (G : GroupScheme S)
    (x : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) :
    x.left ≫ pullback.fst G.X.hom b ≫ G.X.hom = b := by
  rw [pullback.condition, ← Category.assoc]
  have hx : x.left ≫ pullback.snd G.X.hom b = 𝟙 _ := x.w
  rw [hx, Category.id_comp]

/-- The scheme map underlying a base-changed homomorphism commutes with the
projections. -/
theorem baseChange_map_left_fst (b : S' ⟶ S) {G H : GroupScheme S} (f : G ⟶ H) :
    ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Projection of the image of a section under a homomorphism followed by a
base-changed homomorphism. -/
theorem map_comp_baseChange_fst (b : S' ⟶ S) {X : GroupScheme S'} {G H : GroupScheme S}
    (e : X ⟶ (GroupScheme.baseChange b).obj G) (f : G ⟶ H) (z : Over.mk (𝟙 S') ⟶ X.X) :
    (z ≫ (e ≫ (GroupScheme.baseChange b).map f).hom.hom).left ≫ pullback.fst H.X.hom b =
      (z ≫ e.hom.hom).left ≫ pullback.fst G.X.hom b ≫ f.hom.hom.left := by
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact baseChange_map_fst b f (z ≫ e.hom.hom)

/-- Projection of a section under a composite of three homomorphisms. -/
theorem point_comp_three_left {A B C D : GroupScheme S} (x : Over.mk (𝟙 S) ⟶ A.X)
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (x ≫ (f ≫ g ≫ h).hom.hom).left =
      x.left ≫ f.hom.hom.left ≫ g.hom.hom.left ≫ h.hom.hom.left := by
  simp only [Grp.comp_hom_hom, Over.comp_left]

/-- A chain of commutative squares, used to compute projections. -/
theorem comp_eq_of_chain {𝒞 : Type*} [Category 𝒞] {T U V W X Y Z N O Q : 𝒞}
    {z : T ⟶ X} {a : T ⟶ U} {A : U ⟶ V} {B : V ⟶ W} {C : W ⟶ X}
    {p₁ : X ⟶ Y} {p₂ : Y ⟶ Z} {p : W ⟶ Z} {p₃ : V ⟶ N} {p₄ : N ⟶ Z} {p₅ : U ⟶ O}
    {i : O ⟶ N} {r : T ⟶ Q} {s : Q ⟶ O} {m : Q ⟶ Z}
    (e₀ : z = a ≫ A ≫ B ≫ C) (e₁ : C ≫ p₁ ≫ p₂ = p) (e₂ : B ≫ p = p₃ ≫ p₄)
    (e₃ : A ≫ p₃ = p₅ ≫ i) (e₄ : a ≫ p₅ = r ≫ s) (e₅ : m = s ≫ i ≫ p₄) :
    z ≫ p₁ ≫ p₂ = r ≫ m := by
  subst e₀ e₅
  simp only [Category.assoc]
  rw [e₁, e₂, reassoc_of% e₃, reassoc_of% e₄]

section Comparison

variable {U T S₀ S₁ : Scheme.{u}} (f : T ⟶ S₀) (q : U ⟶ T) (a : S₁ ⟶ S₀) (r' : U ⟶ S₁)
  (r : U ⟶ S₀) (hq : q ≫ f = r) (hr : r' ≫ a = r) (G : GroupScheme S₀)
  {P : GroupScheme S₁} (j : (GroupScheme.baseChange a).obj G ≅ P)

/-- Comparison of two iterated base changes of `G` along a commutative square,
followed by an isomorphism of the second intermediate base change. -/
def comparisonIso :
    (GroupScheme.baseChange q).obj ((GroupScheme.baseChange f).obj G) ≅
      (GroupScheme.baseChange r').obj P :=
  Descent.pullbackComparison f q r hq G ≪≫ (Descent.pullbackComparison a r' r hr G).symm ≪≫
    (GroupScheme.baseChange r').mapIso j

/-- The inverse comparison on projections to `G`. -/
theorem comparisonIso_inv_left_fst :
    (comparisonIso f q a r' r hq hr G j).inv.hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q ≫ pullback.fst G.X.hom f =
      pullback.fst P.X.hom r' ≫ j.inv.hom.hom.left ≫ pullback.fst G.X.hom a := by
  simp only [comparisonIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Grp.comp_hom_hom,
    Over.comp_left, Category.assoc, Descent.pullbackComparison_inv_fst,
    Descent.pullbackComparison_hom_fst]
  rw [← Category.assoc, baseChange_map_left_fst, Category.assoc]

/-- The inverse comparison on projections of sections to `G`. -/
theorem comparisonIso_inv_point_fst
    (x : Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange r').obj P).X) :
    (x ≫ (comparisonIso f q a r' r hq hr G j).inv.hom.hom).left ≫
        pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q ≫ pullback.fst G.X.hom f =
      x.left ≫ pullback.fst P.X.hom r' ≫ j.inv.hom.hom.left ≫ pullback.fst G.X.hom a := by
  rw [Over.comp_left, Category.assoc, comparisonIso_inv_left_fst]

/-- The inverse comparison carries coefficient pullback of projections to
canonical descent transport. -/
theorem comparisonIso_inv_descentBasePoint (φ : U ⟶ U) (hφ : φ ≫ q = q)
    (x x' : Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange r').obj P).X)
    (h : x'.left ≫ pullback.fst P.X.hom r' ≫ j.inv.hom.hom.left ≫ pullback.fst G.X.hom a =
      φ ≫ x.left ≫ pullback.fst P.X.hom r' ≫ j.inv.hom.hom.left ≫ pullback.fst G.X.hom a) :
    x' ≫ (comparisonIso f q a r' r hq hr G j).inv.hom.hom =
      descentBasePoint q φ hφ ((GroupScheme.baseChange f).obj G)
        (x ≫ (comparisonIso f q a r' r hq hr G j).inv.hom.hom) := by
  apply baseChange_section_ext q
  rw [descentBasePoint_fst]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [comparisonIso_inv_point_fst, comparisonIso_inv_point_fst]
    exact h
  · have h1 := section_fst_hom q ((GroupScheme.baseChange f).obj G)
      (x' ≫ (comparisonIso f q a r' r hq hr G j).inv.hom.hom)
    have h2 := congrArg (fun t => φ ≫ t) (section_fst_hom q ((GroupScheme.baseChange f).obj G)
      (x ≫ (comparisonIso f q a r' r hq hr G j).inv.hom.hom))
    simp only [Category.assoc] at h1 h2 ⊢
    exact h1.trans (hφ.symm.trans h2.symm)

end Comparison

variable {B : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)

/-- Unfolding of canonical descent transport. -/
theorem descentBasePoint_eq {G : GroupScheme B}
    (x : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X) :
    descentBasePoint b a ha G x =
      baseChangeBasePoint a ((GroupScheme.baseChange b).obj G) x ≫
        (descentBaseChangeIso b a ha G).hom.hom.hom := rfl

/-- Canonical descent transport commutes with base-changed homomorphisms. -/
theorem descentBasePoint_map {G H : GroupScheme B} (f : G ⟶ H)
    (x : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X) :
    descentBasePoint b a ha H (x ≫ ((GroupScheme.baseChange b).map f).hom.hom) =
      descentBasePoint b a ha G x ≫ ((GroupScheme.baseChange b).map f).hom.hom := by
  apply baseChange_section_ext b H
  rw [descentBasePoint_fst, baseChange_map_fst, baseChange_map_fst,
    ← Category.assoc (descentBasePoint b a ha G x).left, descentBasePoint_fst]
  simp only [Category.assoc]

/-- Transport of a Frobenius-type relation through a comparison `esf` and the
quotient comparison `e`.  All objects are variables, so the lemma is
instantiated by its arguments. -/
theorem map_inv_descentBasePoint {k : Type u} [CommRing k] {B' : Scheme.{u}}
    (b' : Spec (CommRingCat.of k) ⟶ B') (a' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k))
    (ha' : a' ≫ b' = b') {G R : GroupScheme B'} (π : G ⟶ R)
    {X Y : GroupScheme (Spec (CommRingCat.of k))}
    (esf : (GroupScheme.baseChange b').obj G ≅ X) (e : (GroupScheme.baseChange b').obj R ≅ Y)
    (proj : X ⟶ Y) (hp : proj ≫ e.inv = esf.inv ≫ (GroupScheme.baseChange b').map π)
    {z z' : rationalPoints X} {w w' : rationalPoints Y}
    (hw : w = rationalPoints.map proj z) (hw' : w' = rationalPoints.map proj z')
    (h : z' ≫ esf.inv.hom.hom = descentBasePoint b' a' ha' G (z ≫ esf.inv.hom.hom)) :
    rationalPoints.map e.inv w' = descentBasePoint b' a' ha' R (rationalPoints.map e.inv w) := by
  subst hw hw'
  have hq : ∀ t : rationalPoints X, rationalPoints.map e.inv (rationalPoints.map proj t) =
      (t ≫ esf.inv.hom.hom) ≫ ((GroupScheme.baseChange b').map π).hom.hom := by
    intro t
    rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, hp, Grp.comp_hom_hom]
  rw [hq, hq, h, descentBasePoint_map]

/-- Combination of `comparisonIso_inv_descentBasePoint` and
`map_inv_descentBasePoint`.  Every object is a variable; the comparison
isomorphism `esf` and the points `x`, `x'` are matched with the comparison form
by heterogeneous equalities, so that the lemma is instantiated by its
arguments. -/
theorem comparison_map_inv_descentBasePoint {K : Type u} [CommRing K]
    {T S₀ S₁ : Scheme.{u}} (f : T ⟶ S₀) (q : Spec (CommRingCat.of K) ⟶ T) (a : S₁ ⟶ S₀)
    (r' : Spec (CommRingCat.of K) ⟶ S₁) (r : Spec (CommRingCat.of K) ⟶ S₀)
    (hq : q ≫ f = r) (hr : r' ≫ a = r) (G : GroupScheme S₀) {P : GroupScheme S₁}
    (j : (GroupScheme.baseChange a).obj G ≅ P)
    (φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)) (hφ : φ ≫ q = q)
    {G' : GroupScheme T} {X : GroupScheme (Spec (CommRingCat.of K))}
    (hG : G' = (GroupScheme.baseChange f).obj G) (hX : X = (GroupScheme.baseChange r').obj P)
    (esf : (GroupScheme.baseChange q).obj G' ≅ X)
    (hesf : HEq esf (comparisonIso f q a r' r hq hr G j))
    {R : GroupScheme T} (π : G' ⟶ R) {Y : GroupScheme (Spec (CommRingCat.of K))}
    (e : (GroupScheme.baseChange q).obj R ≅ Y) (proj : X ⟶ Y)
    (hp : proj ≫ e.inv = esf.inv ≫ (GroupScheme.baseChange q).map π)
    {z z' : rationalPoints X} {w w' : rationalPoints Y}
    (hw : w = rationalPoints.map proj z) (hw' : w' = rationalPoints.map proj z')
    {x x' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((GroupScheme.baseChange r').obj P).X}
    (h : x'.left ≫ pullback.fst P.X.hom r' ≫ j.inv.hom.hom.left ≫ pullback.fst G.X.hom a =
      φ ≫ x.left ≫ pullback.fst P.X.hom r' ≫ j.inv.hom.hom.left ≫ pullback.fst G.X.hom a)
    (hx : HEq x z) (hx' : HEq x' z') :
    rationalPoints.map e.inv w' = descentBasePoint q φ hφ R (rationalPoints.map e.inv w) := by
  subst hG hX
  obtain rfl := eq_of_heq hesf
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hx'
  exact map_inv_descentBasePoint q φ hφ π _ e proj hp hw hw'
    (comparisonIso_inv_descentBasePoint f q a r' r hq hr G j φ hφ x x' h)

/-- Transport of an fppf quotient by a radical along base change and a
comparison isomorphism, when the transported radical has the given range. -/
theorem isFppfQuotient_transport {B₀ B₁ : Scheme.{u}} (b₀ : B₁ ⟶ B₀)
    {G₀ R₀ U₀ : GroupScheme B₀} (i : U₀ ⟶ G₀) (π : G₀ ⟶ R₀)
    (hπ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) π)
    {X V : GroupScheme B₁} (e : (GroupScheme.baseChange b₀).obj G₀ ≅ X) (j : V ⟶ X)
    (h : SubgroupFunctor.range ((GroupScheme.baseChange b₀).map i ≫ e.hom) =
      SubgroupFunctor.range j) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j)
      (e.inv ≫ (GroupScheme.baseChange b₀).map π) := by
  rw [← h, SubgroupFunctor.range_comp_iso, SubgroupFunctor.range_baseChangeHom]
  exact (hπ.baseChange b₀).comapIso e

/-- The underlying scheme map of a homomorphism of group schemes is
quasi-compact when the source is quasi-compact and the target is
quasi-separated over the base. -/
theorem quasiCompact_hom_left {A B : GroupScheme S} (f : A ⟶ B) [QuasiCompact A.X.hom]
    [QuasiSeparated B.X.hom] : QuasiCompact f.hom.hom.left := by
  have : QuasiCompact (f.hom.hom.left ≫ B.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  exact QuasiCompact.of_comp f.hom.hom.left B.X.hom

end General

section Semilinear

open GaloisPointComparison

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Evaluation of a commutative square of group-scheme homomorphisms at a
section. -/
theorem square_point {S : Scheme.{u}} {A A' W Z : GroupScheme S} {m : A ⟶ A'} {φ : A' ⟶ Z}
    {d : A ⟶ W} {p : W ⟶ Z} (h : m ≫ φ = d ≫ p) (x : Over.mk (𝟙 S) ⟶ A.X) :
    (x ≫ d.hom.hom) ≫ p.hom.hom = x ≫ (m ≫ φ).hom.hom := by
  have := congrArg (fun f => x ≫ f.hom.hom) h.symm
  simpa only [Grp.comp_hom_hom, Category.assoc] using this

/-- Evaluation of a commutative square at a section, with both sides
rewritten.  Its implicit objects are meant to be determined by `h`. -/
theorem square_point_eq {S : Scheme.{u}} {A A' W Z : GroupScheme S} {m : A ⟶ A'}
    {φ : A' ⟶ Z} {d : A ⟶ W} {p : W ⟶ Z} (h : m ≫ φ = d ≫ p) (x : Over.mk (𝟙 S) ⟶ A.X)
    {u : Over.mk (𝟙 S) ⟶ W.X} (hu : u = x ≫ d.hom.hom)
    {v : Over.mk (𝟙 S) ⟶ Z.X} (hv : x ≫ (m ≫ φ).hom.hom = v) :
    u ≫ p.hom.hom = v := by
  subst hu
  rw [← hv]
  exact square_point h x

/-- Pulled-back base points are natural for base-changed homomorphisms. -/
theorem baseChangeBasePoint_comp_map {S S' : Scheme.{u}} (a : S' ⟶ S) {X Y : GroupScheme S}
    {Z : GroupScheme S'} (f : X ⟶ Y) (j : (GroupScheme.baseChange a).obj Y ⟶ Z)
    (y : Over.mk (𝟙 S) ⟶ X.X) :
    baseChangeBasePoint a X y ≫ ((GroupScheme.baseChange a).map f ≫ j).hom.hom =
      baseChangeBasePoint a Y (y ≫ f.hom.hom) ≫ j.hom.hom := by
  rw [← Langlands.GroupScheme.baseChangeSectionHom_eq_baseChangeBasePoint,
    ← Langlands.GroupScheme.baseChangeSectionHom_eq_baseChangeBasePoint,
    baseChangeSectionHom_comp_map]

/-- The inner-twisted Galois comparison acts on pulled-back points by twisted
conjugation. -/
theorem baseChangeBasePoint_innerGaloisDescentIso (σ : L ≃ₐ[k] L)
    (z x : rationalPoints (baseChanged k L G)) :
    baseChangeBasePoint (galoisBaseMap k L σ) (baseChanged k L G) x ≫
        (IntegralModel.innerGaloisDescentIso k G σ z).hom.hom.hom =
      z * rationalConjugate k L G σ x * z⁻¹ := by
  change baseChangeBasePoint (galoisBaseMap k L σ) (baseChanged k L G) x ≫
    ((galoisDescentIso k L G σ).hom ≫
      ((baseChanged k L G).innerIso z).hom).hom.hom = _
  rw [Grp.comp_hom_hom, ← Category.assoc, IntegralModel.galoisDescentIso_baseChangeBasePoint,
    comp_innerIso_hom, constantPoint_self]

/-- A generic comparison compatible with the inner-twisted coefficient
transports turns Galois conjugation of points into twisted conjugation. -/
theorem map_rationalConjugate_of_innerGalois
    (c : (L ≃ₐ[k] L) → rationalPoints (baseChanged k L G))
    (ψ : baseChanged k L H ≅ baseChanged k L G)
    (hall : IntegralModel.InnerGaloisCompatible k L H G c ψ) (σ : L ≃ₐ[k] L)
    (y : rationalPoints (baseChanged k L H)) :
    rationalPoints.map ψ.hom (rationalConjugate k L H σ y) =
      c σ * rationalConjugate k L G σ (rationalPoints.map ψ.hom y) * (c σ)⁻¹ := by
  -- The implicit objects of `square_point_eq` are determined by `hall σ`; the
  -- resulting equation is then matched with the stated one.
  have h := square_point_eq (hall σ)
    (baseChangeBasePoint (galoisBaseMap k L σ) (baseChanged k L H) y)
    (rationalConjugate_eq_of_fst k L H σ y _
      (descentBasePoint_fst (baseMap k L) (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) H y))
    ((baseChangeBasePoint_comp_map (galoisBaseMap k L σ) ψ.hom _ y).trans
      (baseChangeBasePoint_innerGaloisDescentIso σ (c σ) _))
  exact h

/-- Stability of a subgroup under all twisted conjugations
`g ↦ c σ * σ(g) * (c σ)⁻¹` by a cocycle `c` implies stability under the inverse
twisted conjugations `g ↦ σ⁻¹((c σ)⁻¹ * g * c σ)`. -/
theorem twisted_inverse_mem (c : (L ≃ₐ[k] L) → rationalPoints (baseChanged k L G))
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate k L G σ (c τ))
    (S : Subgroup (rationalPoints (baseChanged k L G)))
    (hstable : ∀ σ : L ≃ₐ[k] L, ∀ g ∈ S, c σ * rationalConjugate k L G σ g * (c σ)⁻¹ ∈ S) :
    ∀ σ : L ≃ₐ[k] L, ∀ g ∈ S,
      rationalConjugate k L G σ.symm ((c σ)⁻¹ * g * c σ) ∈ S := by
  intro σ g hg
  have h1 : c 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, rationalConjugate_one] at h
    exact mul_left_cancel (h.symm.trans (mul_one (c 1)).symm)
  have h2 : rationalConjugate k L G σ.symm (c σ) = (c σ.symm)⁻¹ := by
    have h := hc σ.symm σ
    rw [show σ.symm * σ = 1 from inv_mul_cancel σ, h1] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  rw [map_mul, map_mul, map_inv, h2, inv_inv]
  exact hstable σ.symm g hg

end Semilinear

section Local

open GaloisPointComparison Langlands.LocalGalois Langlands.LocalGalois.Separable
open Descent.FiniteUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance coreIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance coreIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance coreResidueAlgebra :
    Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

section Core

variable {G H : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F H)
  {P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)}
  {ψ : baseChanged F (inertiaFixedField F) H ≅ baseChanged F (inertiaFixedField F) G}
  (ρ : M.baseChangeUnramified.Iso P ψ)

/-- The projection of an integral section of `P`, transported by `ρ`, to the
original integral model over `𝒪[F]`. -/
def modelProjection (s : P.integralSections) :
    Spec (CommRingCat.of (fixedFieldIntegers F)) ⟶ M.group.X.left :=
  (ρ.integralSectionsEquiv.symm s).left ≫
    pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Morphisms to the generic group over `F` are determined by their structure
morphism and their projection to the integral model. -/
theorem generic_hom_ext {X : Scheme.{u}} {f g : X ⟶ H.X.left}
    (hb : f ≫ H.X.hom = g ≫ H.X.hom)
    (h : f ≫ M.genericIso.inv.hom.hom.left ≫
        pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] F) =
      g ≫ M.genericIso.inv.hom.hom.left ≫
        pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] F)) : f = g := by
  have hiso : IsIso M.genericIso.inv.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map M.genericIso.inv))
  apply (cancel_mono M.genericIso.inv.hom.hom.left).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h
  · have hw : M.genericIso.inv.hom.hom.left ≫
        pullback.snd M.group.X.hom (Spec.algebraMap ↥𝒪[F] F) = H.X.hom :=
      Over.w M.genericIso.inv.hom.hom
    simp only [Category.assoc]
    rw [hw]
    exact hb

/-- The generic value of a point over the inertia field lies over its base. -/
theorem point_fst_hom (x : rationalPoints (baseChanged F (inertiaFixedField F) H)) :
    x.left ≫ pullback.fst H.X.hom (baseMap F (inertiaFixedField F)) ≫ H.X.hom =
      baseMap F (inertiaFixedField F) := by
  rw [pullback.condition, ← Category.assoc]
  have hx : x.left ≫ pullback.snd H.X.hom (baseMap F (inertiaFixedField F)) = 𝟙 _ := x.w
  rw [hx, Category.id_comp]

/-- Projection of the generic value of a base-changed integral section. -/
theorem integralPointMap_projection (v : M.baseChangeUnramified.integralSections) :
    (M.baseChangeUnramified.integralPointMap v).left ≫
        pullback.fst H.X.hom (baseMap F (inertiaFixedField F)) ≫
          M.genericIso.inv.hom.hom.left ≫
            pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] F) =
      Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F) ≫ v.left ≫
        pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) := by
  have h : M.baseChangeUnramified.genericIso.hom.hom.hom.left ≫
        pullback.fst H.X.hom (baseMap F (inertiaFixedField F)) ≫
          M.genericIso.inv.hom.hom.left ≫
            pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] F) =
      pullback.fst (pullback.snd M.group.X.hom
          (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)))
          (Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) ≫
        pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
    M.baseChangeGenericIso_hom_fst (fixedFieldIntegers F) (inertiaFixedField F)
  rw [IntegralModel.integralPointMap_left, Category.assoc, h, ← Category.assoc]
  exact (congrArg (fun t => t ≫
    pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)))
      (pullback.lift_fst _ _ _)).trans (Category.assoc _ _ _)

/-- Canonical integral descent transport induces Galois conjugation of generic
points. -/
theorem integralPointMap_descentBasePoint
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (v : M.baseChangeUnramified.integralSections) :
    M.baseChangeUnramified.integralPointMap
        (descentBasePoint (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
          (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group v) =
      rationalConjugate F (inertiaFixedField F) H σ
        (M.baseChangeUnramified.integralPointMap v) := by
  refine (rationalConjugate_eq_of_fst F (inertiaFixedField F) H σ _ _ ?_).symm
  apply generic_hom_ext M
  · have hy := point_fst_hom (H := H) (M.baseChangeUnramified.integralPointMap
      (descentBasePoint (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
        (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group v))
    have hy' := congrArg (fun t => galoisBaseMap F (inertiaFixedField F) σ ≫ t)
      (point_fst_hom (H := H) (M.baseChangeUnramified.integralPointMap v))
    have ho := galoisBaseMap_over F (inertiaFixedField F) σ
    simp only [Category.assoc] at hy hy' ⊢
    exact hy.trans (ho.symm.trans hy'.symm)
  · have h1 := integralPointMap_projection M (descentBasePoint
      (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) (fixedIntegerBaseAut F σ)
      (fixedIntegerBaseAut_over F σ) M.group v)
    have h2 := integralPointMap_projection M v
    have h3 := descentBasePoint_fst (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
      (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group v
    have h5 := fixedIntegerBaseAut_generic F σ
    have h2' := congrArg (fun t => galoisBaseMap F (inertiaFixedField F) σ ≫ t) h2
    have h3' := congrArg
      (fun t => Spec.algebraMap (fixedFieldIntegers F) (inertiaFixedField F) ≫ t) h3
    have h5' := congrArg (fun t => t ≫ v.left ≫
      pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))) h5
    simp only [Category.assoc] at h1 h2' h3' h5' ⊢
    exact h1.trans (h3'.trans (h5'.symm.trans h2'.symm))

/-- Canonical integral descent transport of the transported section is
twisted conjugation on generic points. -/
theorem integralPointMap_twisted
    {c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hall : IntegralModel.InnerGaloisCompatible F (inertiaFixedField F) H G c ψ)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (u : M.baseChangeUnramified.integralSections) :
    P.integralPointMap (ρ.integralSectionsEquiv
        (descentBasePoint (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
          (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group u)) =
      c σ * rationalConjugate F (inertiaFixedField F) G σ
        (P.integralPointMap (ρ.integralSectionsEquiv u)) * (c σ)⁻¹ := by
  have h1 := ρ.integralPointMap_naturality (descentBasePoint
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group u)
  have h2 := ρ.integralPointMap_naturality u
  have h3 := integralPointMap_descentBasePoint M σ u
  have h4 := map_rationalConjugate_of_innerGalois c ψ hall σ
    (M.baseChangeUnramified.integralPointMap u)
  exact h1.trans ((congrArg (rationalPoints.map ψ.hom) h3).trans
    (h4.trans (congrArg (fun t => c σ * rationalConjugate F (inertiaFixedField F) G σ t *
      (c σ)⁻¹) h2.symm)))

/-- Projection of canonical integral descent transport. -/
theorem modelProjection_twisted (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (u : M.baseChangeUnramified.integralSections) :
    modelProjection M ρ (ρ.integralSectionsEquiv
        (descentBasePoint (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
          (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group u)) =
      fixedIntegerBaseAut F σ ≫ modelProjection M ρ (ρ.integralSectionsEquiv u) := by
  unfold modelProjection
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact descentBasePoint_fst (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group u

/-- Twisted conjugation of integral points corresponds to coefficient pullback
of the projection to the descended model. -/
theorem exists_twisted_section
    {c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hall : IntegralModel.InnerGaloisCompatible F (inertiaFixedField F) H G c ψ)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (s : P.integralSections) :
    ∃ s' : P.integralSections,
      P.integralPointMap s' =
          c σ * rationalConjugate F (inertiaFixedField F) G σ (P.integralPointMap s) *
            (c σ)⁻¹ ∧
        modelProjection M ρ s' = fixedIntegerBaseAut F σ ≫ modelProjection M ρ s := by
  have hs : ρ.integralSectionsEquiv (ρ.integralSectionsEquiv.symm s) = s :=
    MulEquiv.apply_symm_apply _ _
  refine ⟨ρ.integralSectionsEquiv (descentBasePoint
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (fixedIntegerBaseAut F σ) (fixedIntegerBaseAut_over F σ) M.group
    (ρ.integralSectionsEquiv.symm s)), ?_, ?_⟩
  · have h := integralPointMap_twisted M ρ hall σ (ρ.integralSectionsEquiv.symm s)
    rw [hs] at h
    exact h
  · have h := modelProjection_twisted M ρ σ (ρ.integralSectionsEquiv.symm s)
    rw [hs] at h
    exact h

end Core

section Residue

open IsLocalRing

variable {G H : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F H)
  {P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)}
  {ψ : baseChanged F (inertiaFixedField F) H ≅ baseChanged F (inertiaFixedField F) G}
  (ρ : M.baseChangeUnramified.Iso P ψ)

/-- A lift `φ` of the arithmetic Frobenius commutes with reduction, as a square
of spectra. -/
theorem residueBaseMap_frobenius [Fintype 𝓀[F]]
    [Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F))]
    (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hφ : ∀ x : fixedFieldIntegers F,
      residue (fixedFieldIntegers F) (fixedFieldIntegerAut F φ x) =
        residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F]) :
    IntegralModel.residueBaseMap (fixedFieldIntegers F) ≫ fixedIntegerBaseAut F φ =
      galoisBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F))
          (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
            (ResidueField (fixedFieldIntegers F))) ≫
        IntegralModel.residueBaseMap (fixedFieldIntegers F) := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  change residue _ (fixedFieldIntegerAut F φ x) =
    FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] _ (residue _ x)
  rw [hφ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]

/-- The residue comparison identifying the residue-field extension of the
special fibre of `M` with the special fibre of `P`. -/
def specialFibreIso :
    (GroupScheme.baseChange (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)))).obj
        M.specialFibre ≅ P.specialFibre :=
  comparisonIso (IntegralModel.residueBaseMap ↥𝒪[F])
    (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)))
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)) _ rfl
    (fixedResidueBaseMap_square F) M.group ρ.iso

/-- Unfolding of `specialFibreIso`. -/
theorem specialFibreIso_eq :
    specialFibreIso M ρ = comparisonIso (IntegralModel.residueBaseMap ↥𝒪[F])
      (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)))
      (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
      (IntegralModel.residueBaseMap (fixedFieldIntegers F)) _ rfl
      (fixedResidueBaseMap_square F) M.group ρ.iso := rfl

/-- Unfolding of `modelProjection`. -/
theorem modelProjection_eq (t : P.integralSections) :
    modelProjection M ρ t = t.left ≫ ρ.iso.inv.hom.hom.left ≫
      pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) := by
  have h : ρ.integralSectionsEquiv.symm t = rationalPoints.map ρ.iso.inv t := rfl
  unfold modelProjection
  rw [h, rationalPoints.map_apply, Over.comp_left, Category.assoc]

/-- Projection of the reduction of an integral section of `P` to `M`. -/
theorem reduction_projection (t : P.integralSections) :
    (P.reduction t).left ≫
        pullback.fst P.group.X.hom (IntegralModel.residueBaseMap (fixedFieldIntegers F)) ≫
          ρ.iso.inv.hom.hom.left ≫
            pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) =
      IntegralModel.residueBaseMap (fixedFieldIntegers F) ≫ modelProjection M ρ t := by
  rw [modelProjection_eq, IntegralModel.reduction_left, pullback.lift_fst_assoc, Category.assoc]

/-- Projections of reductions related by a Frobenius lift. -/
theorem reduction_projection_frobenius [Fintype 𝓀[F]]
    [Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F))]
    (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hφ : ∀ x : fixedFieldIntegers F,
      residue (fixedFieldIntegers F) (fixedFieldIntegerAut F φ x) =
        residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F])
    (s s' : P.integralSections)
    (h : modelProjection M ρ s' = fixedIntegerBaseAut F φ ≫ modelProjection M ρ s) :
    (P.reduction s').left ≫
        pullback.fst P.group.X.hom (IntegralModel.residueBaseMap (fixedFieldIntegers F)) ≫
          ρ.iso.inv.hom.hom.left ≫
            pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) =
      galoisBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F))
          (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
            (ResidueField (fixedFieldIntegers F))) ≫
        (P.reduction s).left ≫
          pullback.fst P.group.X.hom (IntegralModel.residueBaseMap (fixedFieldIntegers F)) ≫
            ρ.iso.inv.hom.hom.left ≫
              pullback.fst M.group.X.hom (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F)) := by
  rw [reduction_projection, reduction_projection, h, ← Category.assoc,
    residueBaseMap_frobenius φ hφ, Category.assoc]

end Residue

section Assembly

open IsLocalRing

variable {G H : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F H)
  {ψ : baseChanged F (inertiaFixedField F) H ≅ baseChanged F (inertiaFixedField F) G}
  {D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)}

set_option maxHeartbeats 200000 in
/-- The reductive quotient of the special fibre of a smooth model `M` over
`𝒪[F]` whose unramified base change is identified with `D.neutral`: after
residue-field extension and the special-fibre comparison it is an fppf quotient
by the radical of `Q`. -/
theorem exists_residueQuotient
    [Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F))]
    (ρ : M.baseChangeUnramified.Iso D.neutral ψ) (hM : M.IsSmooth)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient) :
    ∃ R : GroupScheme (Spec (CommRingCat.of 𝓀[F])), IsConnectedReductive R ∧
      ∃ π : M.specialFibre ⟶ R,
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
          ((specialFibreIso M ρ).inv ≫ (GroupScheme.baseChange (algebraBaseMap 𝓀[F]
            (ResidueField (fixedFieldIntegers F)))).map π) := by
  have : Smooth M.group.X.hom := hM
  have : Smooth M.specialFibre.X.hom := by
    change Smooth (pullback.snd M.group.X.hom (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  have : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd M.group.X.hom (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  have : ConnectedSpace M.specialFibre.X.left :=
    M.hasConnectedSpecialFibre_of_hasConnectedFibres
      (M.hasConnectedFibres_of_baseChangeUnramified
        (connectedFibres_of_iso ρ.iso D.neutral_connectedFibres))
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence 𝓀[F] M.specialFibre
  obtain ⟨R, π, hπ, hR⟩ := unipotentRadicalQuotient 𝓀[F] M.specialFibre U i hi
  have hRc : IsConnectedReductive R := (perfectFieldPseudoReductive 𝓀[F] R).mp hR
  have hj := ((separableAlgebraicUnipotentRadical 𝓀[F] (ResidueField (fixedFieldIntegers F))
    M.specialFibre inferInstance inferInstance inferInstance).1 U i hi).comp_iso
      (specialFibreIso M ρ)
  exact ⟨R, hRc, π, isFppfQuotient_transport
    (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F))) i π hπ
    (specialFibreIso M ρ) Q.radicalInclusion (hj.range_eq hQ.1)⟩

set_option maxHeartbeats 200000 in
/-- Frobenius compatibility of the reductive quotient transported through a
quotient comparison `e` satisfying `he`. -/
theorem residueQuotient_frobenius [Fintype 𝓀[F]]
    [Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F))]
    (ρ : M.baseChangeUnramified.Iso D.neutral ψ)
    {c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hall : IntegralModel.InnerGaloisCompatible F (inertiaFixedField F) H G c ψ)
    (Q : SpecialFibreQuotientData D)
    (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hφ : ∀ x : fixedFieldIntegers F,
      residue (fixedFieldIntegers F) (fixedFieldIntegerAut F φ x) =
        residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F])
    {R : GroupScheme (Spec (CommRingCat.of 𝓀[F]))} (π : M.specialFibre ⟶ R)
    (e : (GroupScheme.baseChange (algebraBaseMap 𝓀[F]
      (ResidueField (fixedFieldIntegers F)))).obj R ≅ Q.quotient)
    (he : Q.projection ≫ e.inv = (specialFibreIso M ρ).inv ≫
      (GroupScheme.baseChange (algebraBaseMap 𝓀[F]
        (ResidueField (fixedFieldIntegers F)))).map π)
    (g : D.neutral.integralPoints)
    (hg : c φ * rationalConjugate F (inertiaFixedField F) G φ g * (c φ)⁻¹ ∈
      D.neutral.integralPoints) :
    rationalPoints.map e.inv (Q.parahoricReduction ⟨_, hg⟩) =
      descentBasePoint
        (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)))
        (galoisBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F))
          (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
            (ResidueField (fixedFieldIntegers F))))
        (galoisBaseMap_over 𝓀[F] (ResidueField (fixedFieldIntegers F))
          (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
            (ResidueField (fixedFieldIntegers F))))
        R (rationalPoints.map e.inv (Q.parahoricReduction g)) := by
  obtain ⟨s, rfl⟩ := D.neutralSectionsEquiv.surjective g
  obtain ⟨s', hs'1, hs'2⟩ := exists_twisted_section M ρ hall φ s
  have hgs : (⟨_, hg⟩ : D.neutral.integralPoints) = D.neutralSectionsEquiv s' :=
    Subtype.ext hs'1.symm
  exact comparison_map_inv_descentBasePoint (IntegralModel.residueBaseMap ↥𝒪[F])
    (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)))
    (Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F))
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)) _ rfl
    (fixedResidueBaseMap_square F) M.group ρ.iso
    (galoisBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F))
      (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F))))
    (galoisBaseMap_over 𝓀[F] (ResidueField (fixedFieldIntegers F))
      (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F))))
    (G' := M.specialFibre) (X := D.neutral.specialFibre) rfl rfl
    (specialFibreIso M ρ) HEq.rfl π e Q.projection he
    (Q.parahoricReduction_neutralSectionsEquiv s)
    ((congrArg Q.parahoricReduction hgs).trans (Q.parahoricReduction_neutralSectionsEquiv s'))
    (reduction_projection_frobenius M ρ φ hφ s s' hs'2) HEq.rfl HEq.rfl

set_option maxHeartbeats 200000 in
/-- The Frobenius descent of the reductive quotient for a smooth model `M`
over `𝒪[F]` whose unramified base change is identified with `D.neutral`
through a generic comparison compatible with the inner twist `c`. -/
theorem exists_residueDescent [Fintype 𝓀[F]]
    [Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F))]
    (ρ : M.baseChangeUnramified.Iso D.neutral ψ) (hM : M.IsSmooth)
    {c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G)}
    (hall : IntegralModel.InnerGaloisCompatible F (inertiaFixedField F) H G c ψ)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)
    (φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hφ : ∀ x : fixedFieldIntegers F,
      residue (fixedFieldIntegers F) (fixedFieldIntegerAut F φ x) =
        residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F]) :
    ∃ R : GroupScheme (Spec (CommRingCat.of 𝓀[F])), IsConnectedReductive R ∧
      ∃ e : (GroupScheme.baseChange (algebraBaseMap 𝓀[F]
          (ResidueField (fixedFieldIntegers F)))).obj R ≅ Q.quotient,
        ∀ (g : D.neutral.integralPoints)
          (hg : c φ * rationalConjugate F (inertiaFixedField F) G φ g * (c φ)⁻¹ ∈
            D.neutral.integralPoints),
          rationalPoints.map e.inv (Q.parahoricReduction ⟨_, hg⟩) =
            descentBasePoint
              (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)))
              (galoisBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F))
                (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                  (ResidueField (fixedFieldIntegers F))))
              (galoisBaseMap_over 𝓀[F] (ResidueField (fixedFieldIntegers F))
                (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                  (ResidueField (fixedFieldIntegers F))))
              R (rationalPoints.map e.inv (Q.parahoricReduction g)) := by
  obtain ⟨R, hRc, π, hp⟩ := exists_residueQuotient M ρ hM Q hQ
  have : IsAffineHom R.X.hom := hRc.isAffineHom
  have : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap 𝓀[F]
      (ResidueField (fixedFieldIntegers F)))).obj R).X.hom := by
    change IsAffineHom (pullback.snd R.X.hom
      (algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F))))
    infer_instance
  have : IsAffineHom D.neutral.specialFibre.X.hom :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ D.neutral.affine
  have : QuasiCompact Q.projection.hom.hom.left := quasiCompact_hom_left Q.projection
  have : QuasiCompact ((specialFibreIso M ρ).inv ≫ (GroupScheme.baseChange (algebraBaseMap 𝓀[F]
      (ResidueField (fixedFieldIntegers F)))).map π).hom.hom.left := quasiCompact_hom_left _
  exact ⟨R, hRc, FppfQuotientComparison.iso hp hQ.2.1, fun g hg =>
    residueQuotient_frobenius M ρ hall Q φ hφ π (FppfQuotientComparison.iso hp hQ.2.1)
      (FppfQuotientComparison.fac hQ.2.1 hp) g hg⟩

end Assembly

end Local

end TwistedResidueFrobenius

open GaloisPointComparison Langlands.LocalGalois.Separable in
set_option maxHeartbeats 400000 in
/-- Proof of `UnramifiedTwistedReductiveQuotientDescentStatement`: Frobenius
descent of the reductive quotient of a twisted-stable unramified model. -/
theorem unramifiedTwistedReductiveQuotientDescent :
    UnramifiedTwistedReductiveQuotientDescentStatement.{u} := by
  intro F _ _ _ _ G _ c hc hfin D hstable Q hQ φ hφ
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨E, hE, hgal, hfinE, hunram, ⟨N, ⟨e⟩⟩, d, hd, hall⟩ :=
    IntegralModel.exists_common_finiteInnerRecovery F G D.neutral D.neutral_smooth c hc hfin
  have hrec := IntegralModel.recovery_at_liftAutomorphism F E G c d hall
  have hstable' := TwistedResidueFrobenius.twisted_inverse_mem c hc
    D.neutral.integralPoints hstable
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  have : Algebra.IsAlgebraic 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgebraic
  exact TwistedResidueFrobenius.exists_residueDescent
    (IntegralModel.givenFiniteInnerModel F E G N D.neutral e c d hrec D.neutral_smooth
      hstable hstable' hd hunram)
    (IntegralModel.givenFiniteInnerModelIso F E G N D.neutral e c d hrec D.neutral_smooth
      hstable hstable' hd hunram)
    (IntegralModel.givenFiniteInnerModel_smooth F E G N D.neutral e c d hrec D.neutral_smooth
      hstable hstable' hd hunram)
    (IntegralModel.finiteInnerInertiaGenericComparison_innerGaloisCompatible F E G N D.neutral
      e c d hrec D.neutral_smooth hstable hstable' hd hunram hall)
    Q hQ φ hφ

end Langlands.BruhatTits.IntegralModels
