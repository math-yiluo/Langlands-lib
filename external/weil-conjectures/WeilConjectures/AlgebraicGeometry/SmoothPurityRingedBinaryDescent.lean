/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import Mathlib.CategoryTheory.Triangulated.Basic

/-! # Binary descent for ringed coefficient towers

Source: Stacks Project, Tag 08DG, lemma `glue` in `cohomology.tex`;
the strict-system refinement in the smooth-purity blueprint
(blueprint: lem-sp-ringed-tower-binary-descent).

Restriction and direct image are transported from the section-preserving
`SpTowerShriek.Geometry` of the actual small pro-etale topoi. Its `pull_eq`,
`push_eq` and adjunction normalization identify them with the geometric
semilinear operations; no free restriction or direct-image functor is supplied.
The overlap comparison is built from restriction composition. The triangle
arrows are the smaller-open adjunction units followed by the canonical
right-adjoint composition comparison, and by the given overlap map on the U side.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

/-- The fixed support and Tor intervals used by the normalized-tower clause.
Source: the statement of `lem-sp-ringed-tower-binary-descent` in the smooth-purity
blueprint. -/
def spHasFixedBounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (C : spDerivedCoefficientTowers l E T D)
    (a b c d : ℤ) : Prop :=
  a ≤ b ∧ c ≤ d ∧ ∀ n : ℕ,
    (∀ i : ℤ, (i < a ∨ b < i) → IsZero
      ((@DerivedCategory.homologyFunctor
        (Scheme.proEtaleRingModules T
          (Scheme.proEtaleConstantRing T
            (Padic.coefficientExtensionIntegers l E ⧸
              spEllIdeal l E ^ (n + 1))))
        _ _ (HasDerivedCategory.standard _) i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj C))) ∧
    Scheme.HasProEtaleTorAmplitude T
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
      ((spDerivedCoefficientEvaluation l E T D n).obj C) c d

/-- The actual restriction functor transported from the section-normalized
semilinear tower calculus to the recorded coefficient-tower category.
Source: semilinear derived sections and section-preserving tower realization
(blueprint: lem-sp-ringed-tower-binary-descent). -/
abbrev spActualRestriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y) :
    spDerivedCoefficientTowers l E X D_X ⥤
      spDerivedCoefficientTowers l E Y D_Y :=
  (spTowerShriekRealization l E b X D_X).functor ⋙
    SpTowerShriek.pull l E b (o.geometry f) ⋙
    (spTowerShriekRealization l E b Y D_Y).inverse

/-- The actual total right-derived direct image transported to the recorded
coefficient-tower category. Source: semilinear geometric direct image
(blueprint: lem-sp-ringed-tower-binary-descent). -/
abbrev spActualDirectImage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y) :
    spDerivedCoefficientTowers l E Y D_Y ⥤
      spDerivedCoefficientTowers l E X D_X :=
  (spTowerShriekRealization l E b Y D_Y).functor ⋙
    SpTowerShriek.push l E b (o.geometry f) ⋙
    (spTowerShriekRealization l E b X D_X).inverse

/-- The actual open inverse-image/right-derived-image adjunction after transport
through the section-normalized coefficient equivalences. Source: the actual
semilinear geometric adjunction (blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y) :
    spActualRestriction l E b o f D_X D_Y ⊣
      spActualDirectImage l E b o f D_X D_Y :=
  ((spTowerShriekRealization l E b X D_X).toAdjunction.comp
    (SpTowerShriek.adjunction l E b (o.geometry f))).comp
    (spTowerShriekRealization l E b Y D_Y).symm.toAdjunction

/-- Composition of the actual restrictions, cancelling only the intermediate
section-preserving presentation. Source: the semilinear composition calculus
(blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualRestrictionComp
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y)
    (D_Z : SpCoefficientTowersAbelian l E Z) :
    spActualRestriction l E b o f D_X D_Y ⋙
        spActualRestriction l E b o g D_Y D_Z ≅
      spActualRestriction l E b o (g ≫ f) D_X D_Z :=
  let e := spTowerShriekRealization l E b X D_X
  let m := spTowerShriekRealization l E b Y D_Y
  let n := spTowerShriekRealization l E b Z D_Z
  let p := SpTowerShriek.pull l E b (o.geometry f)
  let q := SpTowerShriek.pull l E b (o.geometry g)
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (e.functor ⋙ p)
      (Functor.isoWhiskerRight m.counitIso q) ≪≫
      Functor.isoWhiskerLeft e.functor (o.comp g f)) n.inverse

/-- The canonical overlap comparison from restriction composition and the
pullback equality. Source: Stacks 08DG
(blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualOverlap
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X U V W : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (wU : W ⟶ U) (wV : W ⟶ V)
    (hW : wU ≫ jU = wV ≫ jV)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_U : SpCoefficientTowersAbelian l E U)
    (D_V : SpCoefficientTowersAbelian l E V)
    (D_W : SpCoefficientTowersAbelian l E W) :
    spActualRestriction l E b o jU D_X D_U ⋙
        spActualRestriction l E b o wU D_U D_W ≅
      spActualRestriction l E b o jV D_X D_V ⋙
        spActualRestriction l E b o wV D_V D_W :=
  spActualRestrictionComp l E b o jU wU D_X D_U D_W ≪≫
    eqToIso (congrArg (fun f ↦ spActualRestriction l E b o f D_X D_W) hW) ≪≫
    (spActualRestrictionComp l E b o jV wV D_X D_V D_W).symm

/-- The direct-image compositor is the unique right-adjoint comparison of the
actual restriction compositor. Source: semilinear adjunction calculus
(blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualDirectComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y)
    (D_Z : SpCoefficientTowersAbelian l E Z) :
    spActualDirectImage l E b o g D_Y D_Z ⋙
        spActualDirectImage l E b o f D_X D_Y ≅
      spActualDirectImage l E b o (g ≫ f) D_X D_Z :=
  (((spActualAdjunction l E b o f D_X D_Y).comp
    (spActualAdjunction l E b o g D_Y D_Z)).ofNatIsoLeft
      (spActualRestrictionComp l E b o f g D_X D_Y D_Z)).rightAdjointUniq
        (spActualAdjunction l E b o (g ≫ f) D_X D_Z)

/-- The restriction-unit arrow into the image from a smaller open.
Source: Stacks 08DG (blueprint: lem-sp-ringed-tower-binary-descent). -/
def spActualRestrictionUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_Y : SpCoefficientTowersAbelian l E Y)
    (D_Z : SpCoefficientTowersAbelian l E Z)
    (A : spDerivedCoefficientTowers l E Y D_Y) :
    (spActualDirectImage l E b o f D_X D_Y).obj A ⟶
      (spActualDirectImage l E b o (g ≫ f) D_X D_Z).obj
        ((spActualRestriction l E b o g D_Y D_Z).obj A) :=
  (spActualDirectImage l E b o f D_X D_Y).map
      ((spActualAdjunction l E b o g D_Y D_Z).unit.app A) ≫
    (spActualDirectComparison l E b o f g D_X D_Y D_Z).hom.app
      ((spActualRestriction l E b o g D_Y D_Z).obj A)

/-- Binary descent with the actual section-preserving semilinear operations.
Source: Stacks Project, cohomology.tex, Tag 08DG, lemma-glue; latest smooth-purity
blueprint, Gluing and Uniformity (blueprint: lem-sp-ringed-tower-binary-descent).

Proof (the nine steps of the node):
1. Put D=B|_W. Work in the ordinary derived categories of the entire strict systems, not in the
category of sequences of derived objects. The semilinear-derived-sections node supplies exact
restriction, derived right adjoints, exact evaluations e_n jointly detecting isomorphisms, and
compatibility of evaluations with their units, counits and specified mate maps. At each finite
level, pro-etale open restriction is the subterminal localization in lem-weil-proetale-weakly-
etale-localization. The site is small and subcanonical by proposition-topos-functoriality--1. It
has terminal object X and pullbacks: for any arrows P->C<-Q, the family {id_C,P->C} is a
covering of C in the sense of def-weil-pbc-small-proetale-site, since both maps are weakly etale
and the fpqc condition of definition-small-pro-etale-site--1 is met on every affine open of C by
that open itself inside the identity term; apply the covering base-change axiom to it along
Q->C; thus it has finite limits. Apply lem-sp-subterminal-derived-image-calculus on this finite-
level site with its actual constant ring O/ell^n. It gives self-restriction counit isomorphisms
and the cross-identifications j_U^*Rj_{V*}B_n ≅ Rk_{U*}(B_n|_W), j_U^*Rj_{W*}D_n ≅ Rk_{U*}D_n,
and their V analogues.

2. Construct the same cross-comparisons on systems as counit mates. For example j_U^*Rj_{V*}B ->
Rk_{U*}k_V^*B is adjoint to the restriction to W of the counit j_V^*Rj_{V*}B -> B, with the
canonical iterated restriction. Construct the other comparisons and self-counits likewise. Their
evaluations are exactly those of step 1, hence are isomorphisms; joint detection of isomorphisms
makes the system comparisons isomorphisms. Compose right adjoints using the unique adjunction
comparison for the composite restrictions. Under these identifications the restriction-unit map
r_A:Rj_{U*}A -> Rj_{W*}(A|_W) restricts on U to the unit A -> Rk_{U*}(A|_W), on V to the
identity of Rk_{V*}(A|_W), and on W to the identity of A|_W; r_B has the symmetric descriptions.
These are identities of the specified mate words: transpose the displayed counit definition and
cancel unit-counit pairs by the two adjunction triangle identities. The ordinary mate-pasting
compatibility in lem-coef-semilinear-derived-sections licenses precisely these cancellations on
systems. We use level evaluations only to detect invertibility, never equality of arbitrary
derived morphisms.

3. Let P=Rj_{U*}A ⊕ Rj_{V*}B, Q=Rj_{W*}D, rho_U=Rj_{W*}(c) r_A and rho_V=r_B. In D_X choose a
fibre triangle H --h--> P --(rho_U-rho_V)--> Q -> H[1]. It exists by the cone and rotation
axioms of the triangulated derived category. Define a:H|_U -> A and b:H|_V -> B by restricting
h, projecting to the appropriate summand, and applying the self-counits of step 2. Restriction
is exact, so its derived functor is triangulated and preserves these triangles. This choice
requires neither a functorial cone nor normalization of the coefficient systems.

4. On U, set C=Rk_{U*}D and t=Rk_{U*}(c) eta_A:A->C. Steps 1–2 identify the restricted second
arrow with (t,-1):A⊕C->C and a with projection of h_U to A. This arrow has section z |-> (0,-z),
also after every shift. For any object Z, exactness of Hom(Z,-) on this triangle and its
rotations therefore makes Hom(Z,h_U) injective with image the pairs (x,t x). Indeed the section
makes the boundary after C zero; the shifted section makes the preceding boundary into H|_U
zero; exactness gives injectivity and the asserted kernel image. Projection onto x is
consequently a bijection Hom(Z,H|_U)->Hom(Z,A). For Z=A choose s:A->H|_U mapping to 1_A, so
as=1_A. For Z=H|_U, injectivity gives sa=1 since a(sa)=a. Thus a is an isomorphism. This is the
explicit split-epimorphism calculation in Tag 08DG, rather than an assumption of derived-object
descent.

5. On V put C'=Rk_{V*}(A|_W), C''=Rk_{V*}D, d=Rk_{V*}(c):C'≅C'' and s=eta_B:B->C''. The
restricted second arrow is (d,-s):C'⊕B->C''. Reidentify the first summand by d. The arrow
becomes (1,-s):C''⊕B->C'', with section z |-> (z,0). Exactness of Hom(Z,-), using this section
and its shift, identifies Hom(Z,H|_V) injectively with the kernel pairs (s y,y); projection to y
is bijective onto Hom(Z,B). For Z=B obtain r with br=1_B, and injectivity for Z=H|_V gives rb=1.
Therefore b is an isomorphism. On W the arrow rho_U-rho_V becomes (c,-1), by the actual mate
identities of step 2. Consecutive maps in a distinguished triangle compose to zero, so
restricting (rho_U-rho_V)h=0 gives c(a|_W)-(b|_W)=0 in D_W itself. This proves the required
overlap equation with its specified orientation.

6. Evaluate H at n. Exact evaluation and its commutation with open restriction identify
H_n|_U≅A_n and H_n|_V≅B_n. Exact restriction commutes with kernels, images and cokernels, hence
with each cohomology sheaf. If i is outside [a_0,b_0], the module sheaf H^i(H_n) vanishes on U
and V. On every pro-etale object T->X the base changes T×_X U and T×_X V are open subschemes of
T covering it; open immersions are weakly etale, and every affine open of T is covered by
finitely many affine opens each contained in one of them (quasi-compactness), so they form a
covering of T by definition-small-pro-etale-site--1; the sheaf separatedness axiom then forces every
section of H^i(H_n) to be zero. Thus H^i(H_n)=0 outside precisely the same interval,
independently of n.

7. Fix n and i and put F=H^i(H_n). Take finite stratifications S_alpha of U and T_beta of V
witnessing intrinsic constructibility of F|_U and F|_V. Retain all S_alpha, with their
immersions into X. In each scheme T_beta take the reduced induced closed subscheme C_beta on the
closed subset T_beta minus the inverse image of U. The reduced-induced-closed-subscheme node
supplies this actual scheme and its map C_beta->T_beta. The composites C_beta->T_beta->V->X are
immersions: writing T_beta as closed in an open of V, a closed subscheme of T_beta remains
closed there. Their images, together with the S_alpha, are disjoint locally closed subsets and
partition X. They are constructible in X: a descending chain of closed subsets stabilizes on
each of the finitely many affine charts, since the corresponding ascending chain of radical
ideals stabilizes (the union ideal is finitely generated and hence appears at a finite stage).
Thus X is topologically Noetherian, and def-weil-constructible-subset gives that locally closed
subsets are constructible. The construction is finite, but need not be uniform in n or i.

8. For the open immersions U->X and V->X, the actual module inverse image of def-weil-proetale-
constructible-sheaf is the slice restriction used for H_n|_U and H_n|_V, by lem-weil-pbc-
proetale-ringed-open-comparison together with the constant-ring identification of lem-weil-
proetale-weakly-etale-localization (2); composing with the stratum maps by the pullback-
composition node, on S_alpha F restricts to the specified locally constant finite-stalk module
sheaf coming from A_n. On C_beta, it is the actual module inverse image along C_beta->T_beta of
the corresponding locally constant finite-stalk restriction coming from B_n: canonical constant-
coefficient pullback composition supplies this identification. The finite-local-constancy-
pullback node applies to that scheme morphism and finite ring O/ell^n, so this restriction again
is locally constant and has finite module stalks at every geometric point. Consequently the
preceding global stratification witnesses constructibility exactly in def-weil-proetale-
constructible-sheaf. If X is empty one may retain one empty stratum with its zero module sheaf,
meeting the N>=1 convention. No common stratification, compatible etale origin across levels, or
normalization is used.

9. For an arbitrary module sheaf M over (O/ell^n)_X in degree zero, use the derived tensor
pullback isomorphism on each open. Because the coefficient identification is an isomorphism and
open restriction is exact, its left derived pullback is ordinary restriction. Thus (H_n⊗^L
M)|_U≅A_n⊗^L(M|_U), and similarly on V. The hypotheses give zero cohomology outside [u_0,v_0]
for both restrictions. The sheaf-local vanishing argument of step 6 therefore gives the same
vanishing on X. Since M was arbitrary, the definition of Tor amplitude gives amplitude [u_0,v_0]
for H_n, with no widening and independently of n. Together with steps 6–8 this says exactly that
H lies in the full subcategory of uniformly bounded constructible finite-Tor towers specified in
prose-09-21; this is the ambient category C_X, not its separately defined
normalized subcategory. -/
theorem spRingedTowerBinaryDescent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X U V : Scheme.{u})
    (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    [IsNoetherian X]
    (hcover : Set.range jU.base ∪ Set.range jV.base = Set.univ)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D_X : SpCoefficientTowersAbelian l E X)
    (D_U : SpCoefficientTowersAbelian l E U)
    (D_V : SpCoefficientTowersAbelian l E V)
    (D_W : SpCoefficientTowersAbelian l E (Limits.pullback (C := Scheme) jU jV))
    (A : spDerivedCoefficientTowers l E U D_U)
    (B : spDerivedCoefficientTowers l E V D_V)
    (c : (spActualRestriction l E b o (Limits.pullback.fst jU jV) D_U D_W).obj A ≅
      (spActualRestriction l E b o (Limits.pullback.snd jU jV) D_V D_W).obj B) :
    ∃ (H : spDerivedCoefficientTowers l E X D_X)
      (a : (spActualRestriction l E b o jU D_X D_U).obj H ≅ A)
      (bb : (spActualRestriction l E b o jV D_X D_V).obj H ≅ B)
      (h : H ⟶ (spActualDirectImage l E b o jU D_X D_U).obj A ⊞
        (spActualDirectImage l E b o jV D_X D_V).obj B)
      (δ : (spActualDirectImage l E b o (Limits.pullback.fst jU jV ≫ jU)
        D_X D_W).obj ((spActualRestriction l E b o (Limits.pullback.snd jU jV)
          D_V D_W).obj B) ⟶ H⟦(1 : ℤ)⟧),
      (spActualOverlap l E b o jU jV (Limits.pullback.fst jU jV)
        (Limits.pullback.snd jU jV) (Limits.pullback.condition) D_X D_U D_V D_W).hom.app H ≫
          (spActualRestriction l E b o (Limits.pullback.snd jU jV) D_V D_W).map bb.hom =
        (spActualRestriction l E b o (Limits.pullback.fst jU jV) D_U D_W).map a.hom ≫ c.hom ∧
      (Pretriangulated.Triangle.mk h
        (Limits.biprod.desc
          (spActualRestrictionUnit l E b o jU (Limits.pullback.fst jU jV)
            D_X D_U D_W A ≫
            (spActualDirectImage l E b o (Limits.pullback.fst jU jV ≫ jU)
              D_X D_W).map c.hom)
          (-(spActualRestrictionUnit l E b o jV (Limits.pullback.snd jU jV)
            D_X D_V D_W B ≫
            (eqToIso (congrArg (fun f ↦ spActualDirectImage l E b o f D_X D_W)
              (Limits.pullback.condition (f := jU) (g := jV)).symm)).hom.app
                ((spActualRestriction l E b o (Limits.pullback.snd jU jV)
                  D_V D_W).obj B)))) δ ∈ distTriang _) ∧
      ((spConstructibleTorTowers l E U D_U A ∧
        spConstructibleTorTowers l E V D_V B) →
        spConstructibleTorTowers l E X D_X H) ∧
      (∀ a₀ b₀ u₀ v₀ : ℤ,
        (spConstructibleTorTowers l E U D_U A ∧
          spConstructibleTorTowers l E V D_V B) →
        (spHasFixedBounds l E U D_U A a₀ b₀ u₀ v₀ ∧
          spHasFixedBounds l E V D_V B a₀ b₀ u₀ v₀) →
        spHasFixedBounds l E X D_X H a₀ b₀ u₀ v₀)
  := by
    sorry

end AlgebraicGeometry.ProEtale
