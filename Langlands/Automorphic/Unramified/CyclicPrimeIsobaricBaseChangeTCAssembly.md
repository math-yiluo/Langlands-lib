# Assembly of totally complex prime cyclic isobaric base change

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), Chapter III, Theorem 4.2(c), printed pp. 202–203,
constructs base change by applying the cuspidal cases (a) and (b) and
combining the lifts by parabolic induction. The proof on printed p. 206
uses irreducibility of unitary induction and (2.4), printed p. 200, for
uniqueness.
`CyclicPrimeIsobaricBaseChangeTCAssemblyStatement` gives the corresponding
implication for the exact Library statement over a totally complex base
field. Its premises are unitary singleton lift existence over totally
complex bases and Euler constituent recovery over totally complex fields.

`cyclicPrimeIsobaricBaseChangeTC_of_singletons` proves the implication.
The finite-sum theorem inducts on the multiset of constituents to assemble
the singleton lifts into a unitary isobaric datum with actual weak
base-change attachments. For uniqueness, the extension of a
totally complex field is totally complex. Two weak base changes have
the same Euler polynomials cofinitely upstairs, and the supplied
constituent recovery identifies their upper multisets with
multiplicities. The implication retains two independent field universes
and two independent presentation-carrier universes.

`cyclicPrimeIsobaricBaseChangeTC_of_cuspidal` gives the same assembly
using the Library's isobaric forms of parts (a) and (b) as inputs. The
singleton adapter uses either a unitary cuspidal lift or the full
Galois orbit of a regular upper cusp, according to the norm-character
self-twist criterion.
