# Finite local algebras over Henselian local rings

Author: Worker 598.

`Langlands.CommutativeAlgebra.FiniteLocalHenselianStatement.{u,v}` asserts
that a commutative local ring `S`, finite as a module over a Henselian local
commutative ring `R`, is Henselian. The carriers may have different arbitrary
universes. The algebra structure and its module finiteness are inputs. No
Noetherianity, flatness, étaleness, residue-field restriction, or separately
supplied local-map condition is assumed.

This is precisely the Henselianity conclusion of The Stacks Project,
*Commutative Algebra*, version `ed88ff78`, Section 153, Lemma 153.4
(Tag 04GH), assertion (2), printed p.414. The source also concludes that the
finite ring map is local; this proposition only records the Henselianity
conclusion. The registered source is
`stacks-commutative-algebra-chapter-ed88ff78`, readable as
`Stacks Project - Commutative Algebra, full chapter PDF (version ed88ff78).pdf`,
SHA-256 `b035a1f02104906a1820636cd332a0d7962fef3318d207a056634cb14dc86947`.
Worker 598 read the assertion and its proof on p.414 directly. The proof uses
the finite-local-factor characterization in Lemma 153.3, assertion (10).

This module states the proposition and provides no proof. Its intended use
is to apply Henselian section lifting after constructing a local finite
étale extension of a Henselian local base. It does not itself construct such
an extension or a refinement of an étale neighbourhood.
