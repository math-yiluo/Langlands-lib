# Valuative lifts after a dominating extension

Author: Worker 1543.

`HasDominatingValuativeLift` encodes the extension diagram in Stacks Project,
*Morphisms of Algebraic Spaces*, Definition 67.41.1 (Tag 03IX), printed
pp. 82–83. It is a predicate on a supplied pair of sections `x : X(K)` and
`y : Y(A)` for a morphism `f : X ⟶ Y`, where `A` is a valuation ring with
fraction field `K`. It does not assert that any lift exists.

The registered source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, retained folder
`literature/Stacks Project - Properties of Algebraic Spaces and Morphisms of
Algebraic Spaces, full chapter PDFs (version ed88ff78)/`, folder fingerprint
`cfb36cfc55110aebc6c164e21700e0231c545ae581586883cc1505c67292a90f`.
The file is `spaces-morphisms.pdf`, SHA-256
`46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.

The predicate asks for a valuation ring `B` with fraction field `L`, ring maps
`i : A →+* B` and `j : K →+* L`, and a section `a : X(B)`. The ring square
commutes: `(algebraMap B L).comp i = j.comp (algebraMap A K)`.
The map `i` is local, expressed by `IsLocalHom i`. In this situation `i`
is injective: its composite with `B → L` is the composite of the injective
maps `A → K` and `j`. Thus it identifies `A` with a subring of `B`;
locality says that `B` dominates it. The field map `j` is injective
because it is a unital homomorphism between fields.

The first section equation says that `a` restricts over `L` to the scalar
extension of `x`. Both sides live over the same explicitly specified
object `Spec L → Spec K → Spec A → S` of `Over S`; the commutative
ring square provides the other restriction map. The second equation
says that `f(a)` is the pullback of `y` along `Spec B → Spec A`.
The original square equation `f(x) = y|_K` is supplied separately by
statements using this predicate.

These are actual sheaf sections and pullbacks from `Basic.lean`; the
objects and morphism properties of the algebraic spaces are unchanged.
No finiteness or separability condition is imposed on `L/K`.
All rings, fields and schemes lie in the base universe `u`.

The name and section encoding are internal organization of the source
diagram. In particular this module supplies no proof of existence or
descent of a lift.
