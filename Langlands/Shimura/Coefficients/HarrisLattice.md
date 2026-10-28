# Stable lattices in the whole Harris coefficient module

Author: Worker 57.

This derived construction assembles the existing compact-level lattices at
every actual coefficient place above a rational finite place. It constructs a
full lattice in Harris's original tensor coefficient module, with its actual
integral scalar action and the original adelic representation restricted to
the lattice.

The source is Harris (1999), *Galois properties of cohomological automorphic
forms on GL(n)*, Section 3, printed pp. 306–308, registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
On p. 306 Harris fixes an algebraic representation over a number field and
uses the whole coefficient algebra \(L_v=L\otimes_{\mathbb Q}\mathbb Q_v\).
On pp. 307–308 he chooses a stable integral lattice before forming integral
and torsion coefficient functions, beginning with (3.7). The all-place
assembly, the integral embedding and the proofs here are internal deductions
from the imported coefficient splitting and the constructed lattices at one
completion; these pages do not supply the new formulas as separate theorems.
The inverse representation in Harris's function-equivariance formulas is
separate from the ordinary representation restricted here.

Write \(p\) for the finite rational place, \(I=\texttt{FinitePlacesAbove L p}\),
\(K_l=\texttt{FiniteCompletion L l.1}\), and
\(\mathcal O_l=\texttt{CoefficientIntegers l.1}\). These are the actual
completions and valuation rings at the actual places lying above \(p\).
Let
\[
 S=L\otimes_{\mathbb Q}\mathbb Q_p,\qquad
 K=\prod_{l\in I}K_l,\qquad
 R=\prod_{l\in I}\mathcal O_l,\qquad
 H=S\otimes_L W,\qquad V=\prod_{l\in I}(K_l\otimes_L W).
\]
The type aliases `HarrisCoefficientFields` and `HarrisCoefficientIntegers`
are respectively \(K\) and \(R\).

The first, generic part works over a family of commutative rings \(R_i\)
and modules \(V_i\). `finite_dependentProduct` proves finite generation of
the product module over the product of its scalar rings when the index is
finite and every factor is finite over its own scalar ring. For a fixed
coordinate it restricts scalars along the surjective evaluation ring map.
The identity semilinear map is bijective, so the factor remains finite over
the product ring. Mathlib's finite-product module theorem then applies over
this common ring.

`dependentProductSubmodule` consists exactly of vectors whose coordinates
belong to the specified component submodules. Its scalar action is
componentwise over the product ring. `dependentProductSubmoduleEquiv`
identifies its subtype with the product of the component subtypes;
`dependentProductSubmodule_fg` uses this equivalence and the preceding
finite-generation theorem. For component algebras \(R_i\to K_i\) and
compatible scalar towers, `dependentProductSubmodule_isLattice` proves
fullness over \(\prod_i K_i\). Its proof expresses every single-coordinate
vector using span induction in that coordinate, then sums the finitely
many single-coordinate vectors. It does not require the product algebra
itself to be a field.

For the scalar part, `L : Type u` is a number field and `W : Type w` is
any \(L\)-module, with independent universes and no finiteness hypothesis.
Let \(e_S:S\simeq_L K\) be `harrisCoefficientRingEquiv`, and let
\(e:H\simeq_L V\) be `harrisCoefficientEquiv`. The ring homomorphism
`harrisCoefficientIntegersMap` is
\[
 R\longrightarrow S,\qquad
 r\longmapsto e_S^{-1}\bigl((\mathcal O_l\hookrightarrow K_l)(r_l)\bigr).
\]
`harrisCoefficientRingEquiv_integers` proves its component formula, and
`harrisCoefficientIntegersMap_injective` proves injectivity using the
injectivity of the actual valuation-ring inclusions.
`harrisCoefficientIntegersAlgebra` uses this homomorphism to give \(S\)
its \(R\)-algebra structure. The resulting tensor-module action on \(H\)
is the canonical scalar restriction of its original \(S\)-action:
`harrisCoefficientIntegers_smul` states this equality explicitly.

`harrisCoefficientEquiv_smul` proves
\[
 e(sx)=e_S(s)e(x)
\]
by tensor induction, retaining the original coefficient-algebra action.
`harrisCoefficientEquiv_symm_smul` proves the inverse identity.
`harrisCoefficientIntegralEquiv` packages the same underlying bijection
as an \(R\)-linear equivalence for the preceding canonical \(R\)-action
on \(H\) and the componentwise \(R\)-action on \(V\). The integral
action is thus specified by a canonical ring inclusion and proved
compatible with the splitting.

The representation part takes a finite-dimensional rational algebra
`A`, its algebra anti-involution `σ`, a number field `L`, and the actual
algebraic representation
`ρ : (σ.baseChange L).AlgebraicRepresentation W`.
Here `A`, `L` and `W` share universe `u`, as required by the imported
compact-lattice constructors. `harrisProductFieldAction` assembles the
existing `ρ.placeAction p l.1` into an action on \(V\) linear over \(K\).
The group laws, inverses and product-scalar linearity are proved
coordinatewise. Its component formula identifies the action with the
original completion action, also used by `ρ.harrisProductAdelic`.

Now `W` is finite-dimensional over `L`, and `U` is an actual compact
open subgroup of `σ.FiniteAdelicPoints`. For every \(l\in I\), put
\(\Lambda_l=(\texttt{algebraicCompactCoefficientLattice ρ p l.1 U}).carrier\).
This imported constructor supplies a full \(\mathcal O_l\)-lattice,
its stability under `U.subgroup`, and its continuity prerequisite proved
from algebraic naturality. `harrisProductLattice` is the actual
componentwise product
\(\Lambda=\prod_l\Lambda_l\subset V\).
Its membership formula is coordinatewise membership in these particular
lattices. `harrisProductLattice_isLattice` applies the generic product
theorem, proving finite generation over \(R\) and full span over \(K\).
`harrisProductLattice_stable` applies each constructed factor's stability.
`harrisProductLatticeAction` restricts these original component actions
to the integral product subtype.

`harrisLattice` is the \(R\)-submodule
\(\Lambda_H=e^{-1}(\Lambda)\subset H\), formed by `Submodule.comap`
along `harrisCoefficientIntegralEquiv`. Its membership formula uses
the canonical projections into every \(\Lambda_l\).
`harrisLatticeEquiv` restricts \(e\) to an \(R\)-linear equivalence
\(\Lambda_H\simeq_R\Lambda\). `harrisLattice_isLattice` proves that
\(\Lambda_H\) is a full lattice for the original \(S\)-module \(H\):
finite generation transfers through this integral equivalence; fullness
uses span induction in the full \(K\)-span of \(\Lambda\) and the proved
inverse scalar identity to move each scalar back through \(e_S^{-1}\).
The finite-generation assertion uses \(R=\prod_l\mathcal O_l\).

`harrisLattice_stable` proves stability for the original action
`ρ.harrisAdelic p`, restricted to `U.subgroup`. It applies the imported
adelic equivariance of the canonical splitting, followed by the
constructed component lattice stability. `harrisLatticeAction` is this
action restricted to the full lattice subtype; its displayed formula
recovers the original action after the subtype inclusion.
`harrisLatticeEquiv_action` proves that the integral lattice equivalence
intertwines the original restricted action with the integral product
action.

The construction and all intrinsic fullness, linearity and stability
conclusions are proved from the imported constructions. It takes no
chosen lattice or desired intertwining theorem as an additional output
assumption. This unit supplies the integral assembly. Finite reductions,
a simultaneous open congruence kernel, topological local systems, descent,
torsor or covering properties, scheme levels and canonical models are
further parts of the host task.
