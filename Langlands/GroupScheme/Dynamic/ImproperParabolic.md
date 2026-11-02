# Improper dynamic parabolics and their actual quotients

This internal construction isolates the improper cases needed by the general
quotient compactness proof. Its provenance is the definitions of the dynamic
subgroups in `Dynamic.Basic` and elementary group and quotient laws; it does not
invoke an Iwasawa theorem or an algebraic flag variety.

The cocharacter `trivialCocharacter G` is constructed by Yoneda from the natural
constant identity homomorphisms on all test schemes. Its conjugation orbit is
constant. Consequently its centralizer and parabolic subgroup functors are the
whole group. More generally, full centralization on a test scheme implies that
the parabolic is full on that same test scheme, since every centralizing point
has a constant orbit extension. For a commutative group scheme this applies to
every cocharacter and every test scheme.

For an actually full parabolic subgroup, both existing coset carriers are
subsingletons. The proof explicitly applies the defining left-coset and right-coset
relations to two representatives on the usual `G / P` carrier and on
`Langlands.Induction.LeftQuotient P`, respectively. Each subsingleton is
finite and thus compact for its quotient topology, regardless of the topology
on the point group. The objects are the existing quotients of actual group
scheme points; no replacement quotient or topology is defined.

This covers trivial cocharacters and improper parabolics, and includes the
commutative case without rank, field or characteristic restrictions. The general
connected reductive compactness target remains a separate obligation. In
particular this unit does not assert that every rank-zero reductive group is
commutative or that every cocharacter of such a group is central.

Author: Worker 339.
