/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.Field.FieldCurveCompletionInsep
import WeilConjectures.AlgebraicGeometry.Field.FieldCurveNormalizationGoodOpen
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpreadMarkedCurveDiagram
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesFibreDensity

/-!
# Good curve diagrams near a generic point

Source: Stacks Project, More on Morphisms, Tag 0GK7, lemma-make-good-curves,
assertions (1)-(8) (blueprint: lem-weil-pbc-good-curves-generic-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- (blueprint: lem-weil-pbc-good-curves-generic-diagram)
Stacks Project, Tag 0GK7: a separated finitely presented family with generic fibre of
dimension at most one admits a good curve diagram after a finite radicial base cover.

Formalization: the proof below constructs the field normalization and its dense thickening
locus, invokes spreading of the supplied marked diagram, and proves the two fibrewise density
clauses. The DAG node records this revised dependency route. The original ten-step plan is
retained below as the source argument.

Proof plan:

1. Choose an affine neighbourhood of $\eta$ and replace it by its reduction
$\operatorname{Spec}A$. Its map to the original neighbourhood is a surjective closed immersion,
hence finite and universally injective; it will be included in the eventual map $V\to U$. The
point $\eta$ corresponds to a minimal prime $\mathfrak p$ of the reduced ring $A$, and
$A_{\mathfrak p}=\kappa(\mathfrak p)=k$. Base changing $f$ keeps its separated finite-
presentation hypotheses: affine-local finite-presentation base change is the cited ring lemma;
the diagonal and the finite affine covers base change. The geometric generic fibre is unchanged
by reduction of the base.
Inputs: def-weil-pbc-scheme-reduction, lem-weil-pbc-surjective-closed-immersion-universal-
homeomorphism, lem-weil-pbc-minimal-prime-reduced-localization-field, lem-weil-pbc-finite-
presentation-base-change-composition.

2. Apply the field completion lemma to $X_\eta/k$, obtaining $k'/k$, the normalization components
$Y_{i,\eta}$, their dense open immersions into smooth projective geometrically irreducible
$\overline Y_{i,\eta}$, and finite separable constant fields $k_i/k'$. A projective morphism is
proper. Restriction to the dense open makes $Y_{i,\eta}\to\operatorname{Spec}k_i$ smooth, and its
nonemptiness makes it surjective. If the family is empty the generic fibre is empty; the descent
argument below still applies to the empty scheme.
Inputs: lem-weil-pbc-field-curve-completion-insep, lem-pc-projective-proper, lem-weil-pbc-smooth-
restrict-open-subschemes.

3. Realize $k'/k$ on a finite radicial base cover, using a finite tower of degree-$p$ extensions:
induct on $[k'/k]$, apply the intermediate-field lemma to write $k'=M(z)$ with $[k':M]=p$,
construct the tower for the smaller extension $M/k$, and append $M(z)/M$; in characteristic zero
the tower is empty. At a stage with reduced affine base $\operatorname{Spec}B$ and generic
residue field $l$, first shrink to make $p=0$ in $B$, since $p=0$ in $B_{\mathfrak q}=l$. For the
next generator $\beta$ with $\beta^p=a\in l$, shrink again to represent $a$ in $B$, and put
$C=B[t]/(t^p-a)$. This is finite free on $1,t,\ldots,t^{p-1}$. Every field-valued point lifts
after adjoining a root of $t^p-a$, and two roots in any field are equal because $(u-v)^p=0$. Thus
$\operatorname{Spec}C\to\operatorname{Spec}B$ is surjective and universally injective by the
field-point criterion. At $\mathfrak q$, $C\otimes_B l=l(\beta)$, a field, so the unique point
above $\mathfrak q$ has that local ring. Reducing $C$ preserves this local field and gives
another finite radicial surjection. Induct on the tower length; its terminal residue field is
$k'$.
Inputs: lem-weil-pbc-finite-purely-inseparable-degree-p-intermediate, def-weil-pbc-finite-purely-
inseparable-extension, def-weil-radicial-morphism, def-weil-finite-integral-morphism, def-weil-
pbc-scheme-reduction, lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism.

4. All shrinkings on an intermediate finite radicial cover can be effected by shrinking the
original base: if $h:Z\to U$ is that cover and $O\subset Z$ contains the unique point over
$\eta$, remove the closed set $h(Z\setminus O)$ from $U$. Choose a principal open neighbourhood
of $\eta$ inside that remaining open of the original affine base. Its inverse image is contained
in $O$ and is affine by finiteness of $h$. Thus both the original base and its finite cover
remain affine at each stage. Finiteness and closedness of $h$ justify this operation without a
Noetherian assumption. Finite composition and base change preserve finiteness; the pointwise
injectivity after every base change and surjectivity persist under composition. We now have a
reduced affine base $V$ finite, surjective, universally injective over an open $U$ of the
original $S$, whose generic residue field is $k'$. Any later shrinking of $V$ is handled in the
same way, restricting all the diagram objects by base change. For readability call this reduced
affine base $\operatorname{Spec}A$ and its generic field $k$.
Inputs: lem-weil-pbc-finite-closed-map-finite-fibres, lem-weil-pbc-finite-composition, lem-weil-
pbc-finite-morphism-permanence, def-weil-radicial-morphism, lem-weil-pbc-surjective-base-change.

5. Express $k=A_{\mathfrak p}$ as the filtered colimit of $A_a$ for $a\notin\mathfrak p$. The
affine-transition limit of $\operatorname{Spec}A_a$ is therefore $\operatorname{Spec}k$. Apply
object descent to the finitely many $Y_{i,\eta}$, $\overline Y_{i,\eta}$ and
$\operatorname{Spec}k_i$, keeping $X$ as its already specified model. Apply morphism descent to
their finitely many arrows, and eventual equality to the finitely many commuting triangles. A
common later principal localization gives a diagram $\coprod_iY_i\to X$, $Y_i\to\overline Y_i\to
T_i\to\operatorname{Spec}A$, whose generic fibre is the chosen diagram. Every object is of finite
presentation over the affine base and hence qcqs. Every arrow is locally of finite presentation:
on affine charts apply the cited theorem on finite presentation over a finite-type intermediate
algebra.
Inputs: theorem-finite-etale-covers-proper-henselian--2, lem-weil-pbc-limit-affine-
transition, proposition-jacobian-over-ground-field--1,
lem-weil-pbc-finite-presentation-over-finite-type-algebra.

6. Over the generic field $\nu$ is finite and surjective: it is the normalization of the
reduction followed by the surjective closed immersion of the reduction. Use the existing
normalization theorem and finite composition for this assertion. Descend finiteness and
surjectivity of $\nu$, openness of each $j_i$, finite etaleness of $T_i\to V$, smoothness and
surjectivity of $Y_i\to T_i$, and smoothness and properness of $\overline Y_i\to T_i$, using the
respective cited descent statements. Their qcqs and local finite-presentation hypotheses were
established in the preceding step; the weaker local finite-type hypotheses also hold. There are
only finitely many maps, so take common refinements successively. Finiteness and surjectivity
persist by their base-change lemmas, smoothness and open immersion by the eventual conclusions of
the two new descent statements; etaleness is smooth relative dimension zero and is unchanged
under restriction of base. Properness, defined using the diagonal and universal closedness, is
likewise unchanged under base restriction.
Inputs: lem-weil-pbc-reduced-algebraic-normalization-field-change, lem-weil-pbc-surjective-
closed-immersion-universal-homeomorphism, lem-weil-pbc-finite-composition, lem-weil-pbc-descend-
finite, lem-weil-pbc-descend-surjective, lem-weil-pbc-descend-etale, lem-weil-pbc-descend-smooth-
qcqs, lem-weil-pbc-descend-open-immersion-qcqs, lem-weil-pbc-eventually-proper, lem-weil-pbc-
finite-morphism-permanence, lem-weil-pbc-surjective-base-change, def-weil-proper-morphism, def-
sbc-smooth-morphisms.

7. For each $i$, $T_i$ has precisely one point $\eta_i$ above $\eta$, with residue field $k_i$.
Apply local constancy of geometric component count to the proper smooth finite-presentation
morphism $\overline Y_i\to T_i$. The count at $\eta_i$ is one, so there is an open neighbourhood
on which all fibres are geometrically connected. Apply upper semicontinuity of proper fibre
dimension to obtain an open neighbourhood on which the fibres have dimension at most one. Remove
from $V$ the images under the finite maps $T_i\to V$ of the closed complements of these
neighbourhoods. Those images are closed and avoid $\eta$, so this is an allowed shrinking. Thus
all fibres now have both required properties. Properness plus smoothness gives finite
presentation here: the objects are qcqs and smooth implies locally of finite presentation.
Inputs: lem-weil-pbc-proper-flat-geometric-components-locally-constant, lem-weil-pbc-proper-
fibre-dimension-upper-semicontinuous, lem-weil-pbc-finite-closed-map-finite-fibres, lem-pc-
smooth-flat.

8. Apply the reduced algebraic normalization theorem to $(X_\eta)_{\mathrm{red}}$. Its dense
normal open has normalization an isomorphism. View this open on $X_\eta$, whose reduction has the
same underlying space. The normalization map above this open is then the inclusion of its
reduction, a closed immersion surjective on points. Choose a quasi-compact dense subopen $W_\eta$
there: take finitely many affine neighbourhoods, inside that normal open, of the generic points
of the finitely many components indexed by the normalization. Its inverse image meets every
$Y_{i,\eta}$. By the scheme-over-limit lemma $X_\eta$ is the inverse limit of the qcqs $X_{A_a}$.
Descend $W_\eta$ to a quasi-compact open $W$ at a stage using quasi-compact-open descent. The
inverse image of $W$ under the finite $\nu$ is also qcqs, and its map to $W$ is locally of finite
type. Closed-immersion descent therefore makes $\nu^{-1}(W)\to W$ a closed immersion after a
further localization. It is surjective by base change of the surjective $\nu$, so is a
thickening, with no square-zero assertion.
Inputs: lem-weil-pbc-reduced-algebraic-normalization-field-change, def-weil-pbc-scheme-reduction,
lem-weil-pbc-scheme-over-limit, pqf-lem-limit-qc-open-descends, lem-weil-pbc-descend-closed-
immersion, lem-weil-pbc-surjective-base-change, def-sbc-first-order-thickening.

9. Put $W_i=\nu^{-1}(W)\cap Y_i$. The map $W_i\to T_i$ is open: it is the restriction of a smooth
morphism, smooth implies flat and locally of finite presentation, and such maps are open. Its
image contains $\eta_i$ by construction of $W_\eta$. Since $T_i\to V$ is finite, remove from $V$
the closed images of the complements of these open images. After this shrinking every $W_i\to
T_i$ is surjective. Each fibre of $\overline Y_i\to T_i$ is smooth and geometrically connected
and hence geometrically irreducible: after any field extension apply the integral-geometry core
with base the spectrum of that field (integral, with integrally closed local rings), smooth
source the nonempty connected fibre. Its conclusion that the source is integral gives
irreducibility. The nonempty open fibre of $Y_i$ is therefore irreducible too. Its nonempty open
subspace $(W_i)_t$ is dense. For smoothness after a field extension $F/\kappa(t)$, take affine
first-order thickening test data over $F$ and forget the $F$-structure. Formal smoothness over
$\kappa(t)$ supplies a lift to the original fibre; pair it with the given map of the thickening
to $\operatorname{Spec}F$ to obtain a lift to the fibre product. Local finite presentation
follows on affine charts from the cited finite-presentation base-change lemma.
Inputs: lem-weil-pbc-smooth-restrict-open-subschemes, lem-pc-smooth-flat, lem-weil-pbc-flat-lfp-
open, lem-weil-pbc-finite-closed-map-finite-fibres, lem-sbc-smooth-connected-generic-geometry-
core, def-pc-geometrically-irreducible, def-pc-integral-scheme, def-sbc-smooth-morphisms, lem-
weil-pbc-finite-presentation-base-change-composition.

10. Fix $v\in V$ and a nonempty open in the fibre $(Y_i)_v$ of $Y_i\to V$. Choose a point in it
and let $t$ be its image in $T_i$, necessarily above $v$. Intersection with the fibre $(Y_i)_t$
is a nonempty open, so meets the dense open $(W_i)_t$. Thus $(W_i)_v$ is dense in $(Y_i)_v$.
Taking the finite disjoint union shows $\nu^{-1}(W)$ is dense in every fibre of $\coprod_iY_i\to
V$. The map of this fibre onto $(X_V)_v$ is surjective by surjective base change. The image of a
dense subset under a continuous surjection is dense: the inverse image of every nonempty open is
nonempty open and meets the dense subset. Its image is exactly $W_v$ since $\nu$ is surjective.
Consequently $W$ is dense in every fibre of $X_V\to V$. This proves all clauses. If $I$ is empty,
the descended surjection from the empty scheme forces $X_V$ to be empty; choose $W=\varnothing$.
Inputs: lem-weil-pbc-surjective-base-change, lem-weil-pbc-scheme-coproduct-family, def-pc-scheme-
fibre.
-/
theorem exists_good_curves_generic_diagram
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          (∀ v : V, Dense ((pullback.snd f (g ≫ U.ι)).fiberι v ⁻¹' (W : Set _))) ∧
          (∀ (i : Fin n) (s : T i),
            Dense (((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) ⁻¹' (W : Set _))) ∧
          IsThickening (pullback.snd ν W.ι) := by
  let k : Type u := S.residueField η
  let Z := f.fiber η
  let : Z.Over (Spec (.of k)) := f.fiberOverSpecResidueField η
  have : IsSeparated (Z ↘ Spec (.of k)) := by
    change IsSeparated (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have : LocallyOfFiniteType (Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have : QuasiCompact (Z ↘ Spec (.of k)) := by
    change QuasiCompact (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  obtain ⟨K, hK, hkK, hfin, hinsep, n, C, hC, c, Y, B, e, j, L, hLF, hLA,
    q, p, ν, hc, hinj, hcover, hν, hprops, _⟩ :=
    exists_field_curve_completion_insep k Z hdim
  let := hK
  let := hkK
  have := hfin
  have := hinsep
  let := hLF
  let := hLA
  let ZK := pullback (Z ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have hgood := field_curve_normalization_good_open ZK (pullback.snd _ _)
    n C Y hC c e hc hinj hcover
  dsimp only at hgood
  dsimp only [ZK] at hgood
  rw [← hν] at hgood
  obtain ⟨hνfin, hνsurj, W, _, hWcomp, hWthick⟩ := hgood
  have hcomm (i : Fin n) : Sigma.ι Y i ≫ ν ≫ pullback.snd _ _ =
      j i ≫ q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hcp, hjp, _⟩ := hprops i
    rw [hν, Sigma.ι_comp_desc_assoc]
    exact hcp.trans hjp.symm
  have hL (i : Fin n) : Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) :=
    ⟨(hprops i).1, (hprops i).2.1⟩
  have hj (i : Fin n) : IsOpenImmersion (j i) ∧ Nonempty (Y i) := by
    obtain ⟨_, _, ho, _, hn, _⟩ := hprops i
    exact ⟨ho, hn⟩
  have hq (i : Fin n) : Smooth (q i) ∧ IsProper (q i) ∧
      GeometricallyIrreducible (q i) ∧ topologicalKrullDim (B i) ≤ 1 := by
    obtain ⟨_, _, _, _, _, hsm, hproj, hgeom, hdimB, _⟩ := hprops i
    have := hproj
    exact ⟨hsm, inferInstance, hgeom, hdimB⟩
  have hW : (∀ i, Dense ((Sigma.ι Y i ≫ ν) ⁻¹' (W : Set _))) ∧
      IsThickening (pullback.snd ν W.ι) := by
    refine ⟨?_, hWthick⟩
    intro i
    simpa only [hν, Sigma.ι_comp_desc] using hWcomp i
  obtain ⟨U, hηU, V, g, hgfin, hgsurj, hgrad, T, Y', B', t, j', p', ν', hrest⟩ :=
    exists_spread_marked_curve_diagram f η hη K n L Y B j q ν
      ⟨hνfin, hνsurj⟩ hcomm hL hj hq W hW
  obtain ⟨hν'fin, hν'surj, hcomm', ht, hj', hsm, hp', _, W', hW'surj, hW'thick⟩ := hrest
  have := hν'surj
  have hd := good_curves_fibre_density (pullback.snd f (g ≫ U.ι)) n T Y' B' t j' p' ν'
    hcomm' hj' (fun i ↦ (hp' i).1) (fun i s ↦ (hp' i).2.2 s |>.1) W' hW'surj
  exact ⟨U, hηU, V, g, hgfin, hgsurj, hgrad, n, T, Y', B', t, j', p', ν',
    hν'fin, hν'surj, hcomm', ht, hj', hsm, hp', W', hd.1, hd.2, hW'thick⟩

end AlgebraicGeometry
