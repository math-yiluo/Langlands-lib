# Finite-support families in dependent submodules

This internal algebraic helper constructs a submodule of a dependent product
from component submodules and literal finite support. It proves the support
laws, component evaluation, extension of a single component by zero,
extensionality, and restriction along an index map with finite fibers (in
particular, along an injective map).

The scalar semiring and every component module are arbitrary and have
independent universes. No geometric or representation-theoretic finiteness is
assumed. This is an implementation helper for Waldspurger's algebraic direct
sum in VI.3 (printed p.305); the source's actual component spaces enter only
in the semistandard specialization.

The proofs use closure of each component submodule, containment of sum support
in the union, containment of scalar-product support in the original support,
and the finite-preimage theorem for maps with finite fibers. Single-component
extension uses the dependent `Pi.single`; its support is contained in the
singleton of the input index.
