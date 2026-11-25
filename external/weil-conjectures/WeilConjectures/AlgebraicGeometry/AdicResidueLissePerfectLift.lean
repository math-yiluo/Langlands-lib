/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicCompleteHomSections
import WeilConjectures.AlgebraicGeometry.AdicCompleteResidueConservative
import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionHomML
import WeilConjectures.AlgebraicGeometry.AdicResidueFiniteLocalModels
import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# Local perfect lifting from lisse residue complexes

Source: Stacks Project, `proetale.tex`, Tag 09C6; Bhatt--Scholze, Lemma 6.6.8
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Choose a compatible family whose first term has a property attained from every level.
This is the stable-image step of Stacks Tag 09C6. -/
private theorem adicResidue_sections_with_property
    (F : ℕᵒᵖ ⥤ Type w) (hF : F.IsMittagLeffler)
    (p : F.obj (op 0) → Prop)
    (hp : ∀ n : ℕ, ∃ x : F.obj (op n),
      p (F.map (homOfLE (Nat.zero_le n)).op x)) :
    ∃ x : F.sections, p (x.val (op 0)) := by
  classical
  obtain ⟨n, f, hf⟩ := F.isMittagLeffler_iff_eventualRange.mp hF (op 0)
  obtain ⟨x, hx⟩ := hp n.unop
  have hfx : p (F.map f x) := by
    have he : f = (homOfLE (Nat.zero_le n.unop)).op := Subsingleton.elim _ _
    simpa only [he] using hx
  let y : (F.toEventualRanges).obj (op 0) := ⟨F.map f x, hf.symm ▸ ⟨x, rfl⟩⟩
  obtain ⟨z, hz⟩ := Types.surjective_π_app_zero_of_surjective_map
    (Types.limitConeIsLimit F.toEventualRanges)
    (fun n ↦ F.surjective_toEventualRanges hF (homOfLE (Nat.le_succ n)).op) y
  refine ⟨F.toEventualRangesSectionsEquiv z, ?_⟩
  exact (congrArg (fun t : (F.toEventualRanges).obj (op 0) ↦ p t.val) hz).mpr hfx

/-- Conjugated scalar extension carries an invertible finite-level map to an invertible map. -/
private theorem adicResidueHomTower_isIso_zero
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ)
    (f : (adicResidueLocalReduction.{u, v} X J U n).obj T ⟶
      (adicResidueLocalReduction.{u, v} X J U n).obj M) (hf : IsIso f) :
    IsIso ((adicResidueHomTower.{u, v} X J U T M).map (homOfLE (Nat.zero_le n)).op f) := by
  induction n with
  | zero =>
    simpa only [show (homOfLE (Nat.zero_le 0)).op = 𝟙 (op 0) from rfl,
      Functor.map_id_apply] using hf
  | succ n ih =>
    have he : (homOfLE (Nat.zero_le (n + 1))).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE (Nat.zero_le n)).op := Subsingleton.elim _ _
    rw [he, Functor.map_comp_apply]
    dsimp only [adicResidueHomTower]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    change IsIso ((adicResidueHomTower.{u, v} X J U T M).map (homOfLE (Nat.zero_le n)).op
      (adicResidueHomStep.{u, v} X J U T M n f))
    apply ih
    have := hf
    dsimp only [adicResidueHomStep]
    infer_instance

/-- A complete completed-coefficient complex with bounded lisse finite-Tor residue has
bounded finite-projective constant local models. The residue is an etale complex; its
comparison is taken only after derived reduction. The Tor test is written on every
K-flat representative, using the existing total tensor with degree-zero module sheaves.
The covering sieve is on the transported final object. The termwise completed model
uses the canonical constant-ring comparison and ordinary scalar extension.

Source: Stacks Project, proetale.tex, Tag 09C6 and Section 099L; Bhatt--Scholze,
Lemma 6.6.8 and Proposition 6.6.11
(auxiliary; not a blueprint node).

Proof:
1. Choose generators of $J$, possible since $A$ is Noetherian, and put
$N=\operatorname{Res}_{\underline A}M$. The constant/completed coefficient equivalence applies
on $X_{\mathrm{proét}}$: its completed ring is exactly $B_X$, its completeness notion is the
local one in the statement, and it identifies the reductions of $N$ and $M$ compatibly with all
quotient maps. The residue complex $C$ is constructible, using the single stratum $X$ for each
of its finitely many nonzero locally constant cohomology sheaves. Apply the finite-reduction
structure lemma to $N,C,[a,b]$. Write $A_n=A/J^n$, $M_n=M\otimes^L_{B_X}\underline{A_n}$, and
obtain étale $C_n$ with bounded constructible cohomology and Tor amplitude $[a,b]$, and
compatible $\alpha_n,\beta_n$. In particular $M$ is the derived limit of this specified quotient
tower after restricting scalars. No perfectness of $A_n$ over $A$ was invoked.
Uses: lem-weil-pbc-constant-completion-equivalence,
lem-sfb-adic-constructible-finite-reductions.
2. Work on a connected clopen component $Y$ of an affine Noetherian chart of $X$. These form an
open covering. Indeed the underlying affine space is Noetherian by the cited lemma; Noetherian
induction on closed subsets gives finitely many irreducible components (a minimal counterexample
would be reducible into two smaller closed subsets). Grouping those finitely many components by
chains of nonempty intersections gives finitely many connected components; each group and its
complement are finite unions of closed components, hence clopen. Slice restriction is identified
with the pro-étale site of $Y$ by the localization lemma. It is sectionwise restriction, so
preserves products and kernels, and it preserves epimorphisms because their locally lifting
sections lift over the same covering in the slice. It is therefore exact. It preserves constant
sheaves and their inverse limits. Countable products are exact and represent derived products;
consequently restriction takes the quotient Roos triangle, including its completion unit, to the
same triangle on $Y$. Thus $M|_Y$ and $N|_Y$ remain complete and have the restricted compatible
quotient tower. Restriction also commutes with the total tensor calculation on K-flat
resolutions. Apply the finite-reduction structure lemma on $Y$, choosing these restricted
markings, and henceforth replace $X$ by nonempty connected affine $Y$.
Uses: lem-sc-affine-noetherian-underlying-space, lem-weil-proetale-weakly-etale-localization,
lem-weil-proetale-countable-products-exact, lem-weil-derived-countable-products-core,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-adic-constructible-finite-reductions.
3. For each $n$, apply nilpotent-reduction lissity on the étale site with coefficient ring
$A_n$, ideal $J/J^n$, and bounded complex $C_n$. The ideal is nilpotent, $A_n$ is Noetherian
(ideals correspond to ideals of $A$ containing $J^n$), and the normalized reduction of $C_n$
modulo $J/J^n$ is $C_1=C$. Thus all cohomology sheaves of $C_n$ are étale locally constant of
finite type. The connected étale perfect-constancy lemma now applies: the Tor bound and
boundedness were provided in step 1. Fix one geometric point $\bar x$ of $Y$ and put
$E_n=(C_n)_{\bar x}$. It gives a perfect $E_n$ and one étale local constant value $E_n$ for
$C_n$. Take the exact stalk of $\beta_n$. The tensor-pullback comparison gives normalizations
$E_{n+1}\otimes^L_{A_{n+1}}A_n\simeq E_n$. Define the transition $E_{n+1}\to E_n$ as the
scalar-extension unit followed by this normalization, considered first in $D(A_{n+1})$ and then
in $D(A)$. On K-flat representatives the unit is $p\mapsto p\otimes1$ and reassociation is
$(p\otimes u)\otimes v\mapsto p\otimes uv$; hence the stalk normalizations have the same
quotient cocycles as the $\beta_n$.
Uses: lem-weil-pbc-nilpotent-reduction-lissity, lem-sfb-connected-etale-perfect-constant,
prop-weil-pbc-geometric-stalks-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-pur-derived-change-of-rings.
4. Apply algebraic perfect inverse-limit reconstruction to the tower $E_n$ with those
transitions. Its ring hypothesis is the given $A\simeq\varprojlim A/J^n$, and $E_1$ is perfect
by step 3. Obtain a perfect $P\in D(A)$ and projection-induced isomorphisms $P\otimes_A^L
A_n\simeq E_n$ compatible with all transitions. Choose a bounded finite-projective
representative $P^\bullet$. Next take an affine weakly contractible pro-étale covering $\{W_t\to
Y\}$. The weakly contractible clause of the connected perfect-constancy lemma gives, for each
$n$ and each $W=W_t$, an isomorphism
$M_n|_W\simeq\underline{E_n}|_W\simeq\underline{P^\bullet\otimes_A A_n}|_W$. These isomorphisms
need not be compatible, and no such compatibility is presumed in the next step. For every such
$W$, the localization lemma identifies $Y_{\mathrm{proét}}/W$ with $W_{\mathrm{proét}}$.
Restriction is exact, preserves sectionwise products and the finite Koszul tensor complexes, and
therefore preserves their Roos completion unit, since countable products are exact. Hence $M|_W$
is locally derived complete, and restriction of the completed coefficient ring is
$B_Y|_W=\varprojlim_n\underline{A_n}|_W$; this justifies the completion calculation on $W$
below.
Uses: lem-weil-pbc-rlim-perfect-complete, def-pc-perfect-ring-complex,
lem-weil-pbc-proetale-affine-wcontractible-covering-family,
lem-sfb-connected-etale-perfect-constant, lem-weil-proetale-weakly-etale-localization,
lem-weil-proetale-countable-products-exact, lem-weil-derived-countable-products-core,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-constant-completion-equivalence.
5. Fix $W$ and write $B=B_X|_W$, $T=B\otimes_A P^\bullet$, and
$T_n=\underline{P^\bullet\otimes_A A_n}|_W$. Every term of $T$ is the image of an idempotent on
a finite power of $B$. In fact it is the inverse limit of the corresponding idempotent summands
of $\underline{A_n}^{\,r}$, since an image of an idempotent is the equalizer of that idempotent
and the identity. These summands are killed by $J^n$. The torsion-limit completeness theorem
makes $T$ complete after restriction to $\underline A$, and the constant/completed equivalence
makes it complete over $B$. Put $P^\vee=\operatorname{Hom}_A^\bullet(P^\bullet,A)$, with degree
$i$ term $\operatorname{Hom}_A(P^{-i},A)$ and differential $(-1)^{i+1}$ times precomposition by
$d_P$. Set $H=(B\otimes_A P^\vee)\otimes_B^L M|_W$. A finite-projective term is a retract of a
finite free term, so its tensor is exact; a bounded such complex is K-flat. Its tensor with a
product is the product of its tensors: each total degree has only finitely many summands, and
for an idempotent $e$ on a finite free module, its image commutes with products because
$\operatorname{im}(e)=\ker(1-e)$ and products commute with kernels and finite powers. Thus
tensoring the quotient-completion Roos triangle of $M|_W$ with this bounded dual identifies
$H\simeq R\lim_n H_n$, where $H_n=T_n^\vee\otimes_{\underline{A_n}}^L M_n|_W$ are its canonical
reductions. The coefficient-completion lemma identifies this quotient-limit unit with the local
completeness unit, so $H$ is locally complete. By step 4 every $H_n$ is a constant complex with
value $(P^\vee\otimes_A A_n)\otimes_{A_n}(P^\bullet\otimes_A A_n)$. This is perfect, in
particular at $n=1$.
Uses: lem-weil-pbc-torsion-limit-sheaf-completeness,
lem-weil-pbc-constant-completion-equivalence, lem-pc-kflat-closure,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-pur-derived-change-of-rings.
6. For clarity the degree-zero cohomology groups $G_n=H^0(W,H_n)$ are precisely
$\operatorname{Hom}_{D(W_{\mathrm{proét}},A_n)}(T_n,M_n|_W)$. Evaluation on $W$ is exact. The
sheaf $\underline{A_n}$ is therefore projective in the slice module category, since its Hom
functor is evaluation; each term of $T_n$ is a finite direct summand of such free sheaves and is
projective too. Bounded-above projective complexes are K-projective, so the derived-Hom
bijection identifies these morphisms with chain maps modulo chain homotopy. Termwise
finite-projective duality identifies their Hom complex with $T_n^\vee\otimes M_n|_W$: on a
summand of $A_n^r$ the map is $\lambda\otimes m\mapsto(p\mapsto\lambda(p)m)$; for complexes use
the displayed dual differential and the usual tensor sign. Over $B$, exact evaluation gives
$\operatorname{Hom}_B(B,F)=F(W)$, so the finite direct summands of finite free $B$-sheaves in
$T$ are projective. The two cited K-projective statements then identify
$\operatorname{Hom}_{D(B)}(T,M|_W)$ with $H^0$ of the global Hom complex. Evaluation
$\lambda\otimes m\mapsto(p\mapsto\lambda(p)m)$, with the dual differential of step 5, identifies
that complex with the sections of a representative of $H$; exact evaluation identifies its
cohomology with $H^0(W,H)$. These identifications commute with quotient reduction because the
evaluation formula and both differentials commute with the coefficient map $A_{n+1}\to A_n$.
Apply the weakly contractible ML lemma to $\operatorname{Res}H$. Its reductions are the $H_n$ by
coefficient comparison, it is complete by step 5, and its first constant value is perfect.
Therefore the tower $G_n$ has eventually stable images. Each $G_n$ contains an isomorphism by
step 4.
Uses: lem-weil-pbc-proetale-weakly-contractible-evaluation-exact,
lem-sc-bounded-above-projective-kprojective, lem-coef-kprojective-derived-hom-bijection,
lem-sfb-wcontractible-constant-reductions-ml, lem-weil-pbc-constant-completion-equivalence.
7. Let $S_n=\bigcap_{k\geq n}\operatorname{im}(G_k\to G_n)$. The ML property says that this
intersection is an eventual image. The maps $S_{n+1}\to S_n$ are surjective: for fixed $n$,
choose $k$ beyond stabilization at both $n$ and $n+1$ and lift an element of $S_n$ from $G_k$.
Choose $k$ beyond stabilization at $1$ and an isomorphism in $G_k$; its reduction $g_1\in S_1$
is an isomorphism. Repeatedly lift along the surjections $S_{n+1}\to S_n$ to obtain a compatible
sequence $(g_n)$ beginning with $g_1$. Equivalently apply the nonempty-ML-limit lemma to the
fibers over $g_1$ in the stable systems. Apply the sheaf Milnor sequence to the strict quotient
tower $H_n$. The Roos model is a derived limit by exact countable products. Exact evaluation at
$W$ preserves the resulting epimorphism $H^0(H)\twoheadrightarrow\lim_nH^0(H_n)$, and evaluation
commutes with the limit sectionwise. Thus $(g_n)$ lifts to a class in $H^0(W,H)$, hence by step
6 to an actual morphism $g:T\to M|_W$ of $B$-complexes. Its derived reduction modulo $J$ is
$g_1$, an isomorphism. This constructs the compatible map; it does not take a nonfunctorial
limit of independently chosen isomorphisms.
Uses: lem-sfb-wcontractible-constant-reductions-ml, lem-weil-pbc-ml-sets-tower-limit-nonempty,
proposition-milnor-sequence--2, lem-weil-proetale-countable-products-exact,
lem-weil-derived-countable-products-core, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-weil-pbc-proetale-weakly-contractible-evaluation-exact.
8. Let $Q=\operatorname{Cone}(g)$. Local completeness is closed under cones: the
Koszul-completion unit in the constant/completed lemma is a natural map between exact functors
(finite Koszul tensor and the exact derived-limit functor); its cone vanishes at the third
vertex whenever it vanishes at the other two, by the long exact cohomology sequence. Since both
$T$ and $M|_W$ are complete, $Q$ is complete. Its first reduction is zero. All its reductions
are zero: the exact constant sequence $0\to J^n/J^{n+1}\to A/J^{n+1}\to A/J^n\to0$ gives after
derived tensor with $\operatorname{Res}Q$ a triangle whose first term is
$(Q\otimes_B^L\underline{A/J})\otimes_{\underline{A/J}}^L\underline{J^n/J^{n+1}}=0$. Induction
from $n=1$ proves the claim. Constant realization is exact; derived scalar extension preserves
this triangle, and reassociation is the balancing map already written in step 3. Completeness
therefore gives $Q\simeq R\lim_n0=0$. The long exact cohomology sequence shows $g$ is an
isomorphism. On each $W_t$ we have proved exactly $M|_{W_t}\simeq (B_X|_{W_t})\otimes_A
P^\bullet$. The tensor is computed termwise because the finite-projective terms are flat and the
complex is bounded. Assemble the covers over all connected affine components of the original
$X$. If $X$ is empty take the empty cover. All coefficient rings remain the original $A$ and its
quotients; neither finiteness as sets nor quotient perfectness was used.
Uses: lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-sf-derived-homology-long-exact,
lem-weil-pbc-constant-module-section-properties, lem-pur-derived-change-of-rings,
lem-pc-kflat-closure.
-/
theorem adicResidueLissePerfectLift
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A]
    (M : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J))
    (_hcomplete : CategoryTheory.ConstantCompletion.IsComplete
      (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X) A
        J 0) M)
    (C : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A J 0))
    (_hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (_hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (A ⧸ J ^ (0 + 1))
      ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (a b : ℤ) (_hab : a ≤ b)
    (_htor : ∀ P : CategoryTheory.ConstantCompletion.Cx
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := smallModelComparisonEtaleTopology.{u, v} X)
        (R := CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) P →
      Nonempty ((CategoryTheory.ConstantCompletion.Q
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)).obj P ≅ C) →
      ∀ (N : CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0))
        (q : ℤ), q < a ∨ b < q →
        IsZero (adicResidueTensorCohomology.{max v (u + 1)}
          (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X)
            A J 0) P N q))
    (_hres : Nonempty
      ((CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X)
          A J 0)).obj M ≅
        (adicResidueComparison.{u, v} X (A ⧸ J ^ (0 + 1))).obj C)) :
    ∃ S : Sieve ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_ X.ProEt)),
      S ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ (U : coefficientProEtaleSiteModel.{u, v} X)
        (f : U ⟶ (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_
          X.ProEt)), S f →
        ∃ (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ),
          P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
          (∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) ∧
          Nonempty
            ((adicResidueRestriction.{max v (u + 1)}
              (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u,
                v} X) A J) U).obj M ≅
              (adicResidueRestriction.{max v (u + 1)}
                (CategoryTheory.ConstantCompletion.completed
                  (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
                    (adicResidueConstantPerfect.{u, v} X J P)) := by
  classical
  obtain ⟨S, hS, hmodels⟩ := adicResidue_finite_local_models.{u, v} X J M _hcomplete C
    _hbounded _hlisse a b _hab _htor _hres
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨V, R, P, c, d, hc, hd, hP, hAffine, hV, eM, eT, hT, hM, hfinite⟩ :=
    hmodels U f hf
  obtain ⟨eM⟩ := eM
  obtain ⟨eT⟩ := eT
  let B := CategoryTheory.ConstantCompletion.completed
    (coefficientProEtaleModelTopology.{u, v} X) A J
  let T := (adicResidueRestriction B V).obj (adicResidueConstantPerfect X J P)
  let L := (adicResidueRestriction B V).obj M
  let G := adicResidueHomTower.{u, v} X J V T L
  have hML : G.IsMittagLeffler :=
    adicResidueHomTower_mittagLeffler.{u, v} X J V hAffine hV P c d hc hd hP L hM hfinite
  obtain ⟨s, hs⟩ := adicResidue_sections_with_property G hML (fun g ↦ IsIso g) (by
    intro n
    obtain ⟨e⟩ := hfinite n
    exact ⟨e.hom, adicResidueHomTower_isIso_zero.{u, v} X J V T L n e.hom inferInstance⟩)
  obtain ⟨g, hg⟩ := adicResidueHomSection_surjective.{u, v} X J V T L hM s
  have hresidue : IsIso ((adicResidueLocalReduction.{u, v} X J V 0).map g) := by
    have h := congrArg (fun t : G.sections ↦ t.val (op 0)) hg
    change (adicResidueLocalReduction.{u, v} X J V 0).map g = s.val (op 0) at h
    exact h.symm ▸ hs
  have := adicResidue_isIso_of_residue.{u, v} X J V T L hT hM g hresidue
  exact ⟨P, c, d, hc, hd, hP, ⟨eM.symm ≪≫ R.mapIso (asIso g).symm ≪≫ eT⟩⟩

end AlgebraicGeometry.Scheme
