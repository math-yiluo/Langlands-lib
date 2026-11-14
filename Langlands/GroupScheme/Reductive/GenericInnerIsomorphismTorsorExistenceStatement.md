# Existence of the integral inner-isomorphism torsor over a DVR

Worker 684.

`GenericInnerIsomorphismTorsorExistenceStatement` asserts that for every
discrete valuation ring `R` and fraction field `K`, every pair of reductive
group schemes `G, H` over `Spec R` and every prescribed actual isomorphism
`f : G_K ≅ H_K`, there are data `GenericInnerIsomorphismTorsor R K G H f`.
The proposition quantifies in every universe. It assumes neither that `R`
is henselian or complete nor that its residue field is finite.

This is a derived geometric intermediate statement for Conrad, *Reductive
group schemes* (2014), Theorem 7.1.9(1), p.245, the automorphism discussion
p.259 and the proof of Theorem 7.2.16, pp.261–262. The source is registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The statement is a reformulation of the inner-isomorphism fibre used in that
argument, rather than a verbatim numbered theorem.

The geometric route is to form the sheaf of isomorphisms modulo inner
automorphisms. The generic isomorphism defines a generic outer-isomorphism
class. Over the normal local base, its finite étale component permits that
class to extend to the whole DVR. Its fibre in the actual isomorphism sheaf
is the required torsor under the integral adjoint quotient. The generic
point is the original `f`. The integral adjoint action is by inverse
precomposition, and evaluation recovers actual group-scheme isomorphisms
over every test scheme, with the exact action compatibility in the data
structure. Constructing these schemes and verifying their properties are
proof obligations of this statement.

The conclusion does not assert that the torsor has an integral section,
or that `G` and `H` are isomorphic over an arbitrary DVR. For a complete DVR
with finite residue field the published integral torsor point theorem gives
such a section. The separate conditional reduction implements this step
and obtains the full all-test inner-correction equation, including comparison
with an arbitrary supplied generic adjoint quotient.
