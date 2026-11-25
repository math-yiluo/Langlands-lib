/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Affine.Limit.AffineLimitFibreDimensionBoundCore

/-!
# Fibre dimension bounds descend in affine inverse systems

Source: Stacks Project, Limits, Tag 05M5, `lemma-limit-dimension`, affine specialization
(blueprint: lem-weil-pbc-affine-limit-fibre-dimension-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An upper bound on all fibre dimensions of a directed colimit of finite type ring maps
already holds at one stage, provided the base-change comparison maps are surjective.
Source: Stacks Project, Limits, Tag 05M5, `lemma-limit-dimension`, affine specialization
(blueprint: lem-weil-pbc-affine-limit-fibre-dimension-bound).

The comparison is expressed by the commutative-ring pushout, canonically the tensor product
by `CommRingCat.pushoutCoconeIsColimit`. The fibres are affine pullbacks, identified by
`pullbackSpecIso` with spectra of the tensor products with the residue fields. Thus empty
fibres have dimension bottom and are included.

Proof:
1. Put $X_i=\operatorname{Spec}C_i$, $S_i=\operatorname{Spec}A_i$ and let $f_i$ be induced by
$A_i\to C_i$. Define $U_i$ to be the points whose local topological fibre dimension is at most
$d$, and $Z_i=X_i\setminus U_i$. For each $x_i\in U_i$, this local dimension is a nonnegative
integer $n\le d$ (the fibre point exists, so its neighbourhoods are nonempty). The ring-theoretic
bounded-open-upstairs theorem, applied to $A_i\to C_i$ at $x_i$ with this $n$, gives an open
neighbourhood all of whose points have local fibre dimension at most $n$, hence at most $d$. Thus
$U_i$ is open as the union of these neighbourhoods, and $Z_i$ is closed. The affine fibre-product
identification and the supremum-of-local-dimensions theorem say that $Z_i$ is empty exactly when
every fibre of $f_i$ has dimension at most $d$. Assume for contradiction that every $Z_i$ is
nonempty.
2. For $j\ge i$ and $x_j\in X_j$, write $x_i$ for its image and $s_j=f_j(x_j)$, $s_i=f_i(x_i)$.
For a ring map $R\to T$ carrying a prime $\mathfrak q$ of $T$ back to $\mathfrak p$, the induced
injection $R/\mathfrak p\to T/\mathfrak q$ extends to their fraction fields by $a/b\mapsto\bar
a/\bar b$, since $b\notin\mathfrak p$ maps outside $\mathfrak q$; these are the residue fields.
Thus $\kappa(s_i)\to\kappa(s_j)$ is the field map used below. The surjection
$A_j\otimes_{A_i}C_i\to C_j$, after extending scalars to $\kappa(s_j)$, identifies $(X_j)_{s_j}$
with a closed subspace of $(X_i)_{s_i}\times_{\kappa(s_i)}\kappa(s_j)$. Surjectivity after
tensoring is explicit: a pure tensor $c_j\otimes\lambda$ lifts by choosing a preimage of $c_j$,
and sums lift termwise. The quotient-spectrum homeomorphism identifies this as a closed
embedding. At corresponding points, local dimension in a closed subspace is at most that in the
ambient space: choose an ambient open neighbourhood attaining its local dimension; intersect with
the closed subspace, and every chain of irreducible closed subsets of the intersection is a chain
of irreducible closed subsets of that neighbourhood. Taking the minimum over neighbourhoods gives
the inequality. Field-extension invariance of local dimension applies to the finite type
$\kappa(s_i)$-algebra $C_i\otimes_{A_i}\kappa(s_i)$ (the images of any finite set of algebra
generators still generate). Consequently a point of $Z_j$ maps into $Z_i$.
3. Let $J_i$ be the radical ideal defining the reduced induced structure on $Z_i$, and put
$D_i=C_i/J_i$. For $a\in J_i$ and every prime of $C_j$ belonging to $Z_j$, its contraction
belongs to $Z_i$ by step 2, so the image of $a$ lies in that prime. The description of the
reduced induced ideal as the intersection of these primes implies that $C_i\to C_j$ maps $J_i$
into $J_j$. Thus the $D_i$ form a directed ring system. Set $D=\varinjlim D_i$. The
spectrum-colimit theorem identifies $\operatorname{Spec}D$ with the inverse limit of the nonempty
affine schemes $\operatorname{Spec}D_i$, whose transitions are affine. Each is quasi-compact by
quasi-compactness of spectra, so the nonempty-limit theorem supplies a point
$z\in\operatorname{Spec}D$. The compatible maps $C_i\to D$ induce $C\to D$ and hence a point
$x\in\operatorname{Spec}C$ with images $x_i\in Z_i$. No factorization from mere set containment
of an arbitrary nonreduced scheme is used.
4. Let $s$ be the image of $x$ in $\operatorname{Spec}A$, let $k=\kappa(s)$, and let $s_i$ be its
image in $S_i$. Fix $i_0\in I$ and restrict to $i\ge i_0$, a cofinal directed tail. To extend a
compatible cocone from this tail to the whole system, for an arbitrary index $i$ choose $j\ge
i,i_0$ and compose the transition from $i$ to $j$ with its cocone map; a common upper bound of
two choices proves independence and compatibility. This gives the same colimit universal property
on the tail. Put $B_i=C_i\otimes_{A_i}k$, using $A_i\to A\to k$. For $j\ge i$ the map $B_i\to
B_j$ is surjective: extend the given comparison surjection along $A_j\to k$; the source
identifies with $C_i\otimes_{A_i}k$ by $(a_j\otimes c_i)\otimes\lambda\mapsto c_i\otimes\bar
a_j\lambda$, with inverse $c_i\otimes\lambda\mapsto(1\otimes c_i)\otimes\lambda$. The balancing
relations make these ring maps well-defined, and their composites are the identity on pure
tensors. Set $B=C\otimes_Ak$. This is the colimit of the $B_i$: compatible ring maps $B_i\to T$
amount, by the tensor pushout property, to compatible maps $C_i\to T$ and one map $k\to T$ (the
restrictions to $k$ coincide by compatibility at common upper bounds) agreeing on every $A_i$. By
the two colimit universal properties they amount precisely to maps $C\to T$, $k\to T$ agreeing on
$A$, hence to a map $B\to T$. The point $x$ determines a point $\widetilde
x\in\operatorname{Spec}B$, by the tensor pushout map $B\to\kappa(x)$ induced by $C\to\kappa(x)$
and $k\to\kappa(x)$. The field map $k\to\kappa(x)$ sends the fraction of classes $a/b$ to the
fraction of their images; its denominator stays nonzero by contraction of the prime of $x$ to
$s$, so the two maps agree on $A$.
5. The ring $B_{i_0}$ is a finite type $k$-algebra, since the images of the finite generators of
$C_{i_0}$ over $A_{i_0}$ generate it over $k$. A field is Noetherian: its only ideals are zero
and the whole field, generated by zero and one. The finite-type-algebra Noetherian theorem
therefore makes $B_{i_0}$ Noetherian. For $i\ge i_0$ let $K_i=\ker(B_{i_0}\to B_i)$; these ideals
are increasing and form a directed family. The maximal-ideal-in-a-set theorem supplies a maximal
$K_{i_1}$ among them. For $j\ge i_1$ it follows that $K_j=K_{i_1}$; for any other $i$ a common
upper bound shows $K_i\subseteq K_{i_1}$. All maps $B_{i_0}\to B_i$ are surjective. The kernel of
$B_{i_0}\to B$ is exactly $\bigcup_iK_i$: an element maps to zero in the colimit exactly when it
becomes zero at a stage, by the elementwise filtered-colimit theorem. That map is surjective as
well: every colimit element has a representative in some $B_i$, and that representative lifts to
$B_{i_0}$. Hence the canonical map $B_{i_1}\to B$ is an isomorphism, since both are the quotient
of $B_{i_0}$ by $K_{i_1}$. Explicitly, to invert $B_{i_1}\to B$, lift an element of $B$ to $b\in
B_{i_0}$ and send it to the image of $b$ in $B_{i_1}$. Two lifts differ by $K_{i_1}$, so this is
well-defined; it preserves ring operations and is inverse on representatives.
6. The point $\widetilde x$ corresponds under $B_{i_1}\cong B$ to the point lying over $x_{i_1}$
in the field extension of the ordinary fibre of $f_{i_1}$ from $\kappa(s_{i_1})$ to $k$. Its
contraction is exactly the fibre point of $x_{i_1}$, since both points are obtained by
contraction of the maps to $\kappa(x)$. The fibre algebra
$C_{i_1}\otimes_{A_{i_1}}\kappa(s_{i_1})$ is finite type over its field, so local-dimension
field-extension invariance applies. Since $x_{i_1}\in Z_{i_1}$, the local dimension at
$\widetilde x$ of $\operatorname{Spec}B$ is greater than $d$. But the hypothesis bounds the
dimension of this entire fibre by $d$, and its local dimension is at most the entire dimension
(the entire space is an allowed open neighbourhood). This is a contradiction.
7. Therefore some $Z_i$ is empty. At that stage every point of every fibre has local dimension at
most $d$. Taking the supremum over the points of each fibre gives the asserted global bound. For
an empty fibre this supremum is $-\infty$, so it imposes no exception. -/
theorem exists_stage_fibre_dimension_le
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (A C : I ⥤ CommRingCat.{u}) (φ : A ⟶ C)
    (hfinite : ∀ i : I, (φ.app i).hom.FiniteType)
    (hsurj : ∀ (i j : I) (hij : i ≤ j),
      Function.Surjective
        (pushout.desc (φ.app j) (C.map (homOfLE hij))
          (φ.naturality (homOfLE hij))).hom)
    (d : ℕ)
    (hbound : ∀ (p : Ideal ↥(colimit A)) [p.IsPrime],
      topologicalKrullDim
        ↥(pullback (Spec.map (colimMap φ))
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(colimit A) p.ResidueField))) : Scheme.{u}) ≤
        (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ (p : Ideal (A.obj i)) [p.IsPrime],
      topologicalKrullDim
        ↥(pullback (Spec.map (φ.app i))
          (Spec.map (CommRingCat.ofHom (algebraMap (A.obj i) p.ResidueField))) : Scheme.{u}) ≤
        (d : WithBot ℕ∞) := by
  classical
  by_contra h
  apply fibre_dimension_contradiction_of_all_stages_bad A C φ hfinite hsurj d hbound
  intro i
  push Not at h
  obtain ⟨p, hp, hdim⟩ := h i
  exact ⟨⟨p, hp⟩, hdim⟩

end AlgebraicGeometry
