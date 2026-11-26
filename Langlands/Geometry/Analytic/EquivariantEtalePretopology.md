# The equivariant étale pretopology

`equivariantEtalePretopology X` equips the existing category of étale
`G`-morphisms to a `G`-space `X` with its jointly surjective covering families.
This upgrades `equivariantEtalePrecoverage X` to a pretopology. Its generated
Grothendieck topology is `equivariantEtaleTopology X`.

An arrow in the site is étale on underlying spaces by right cancellation of
étale maps. Take a localized analytic pullback of a cospan and its étale
second projection. Its continuous diagonal action makes the pullback an
equivariant site object because the composite of the second projection and
the second structure map is étale. The pullback is universal in the site:
the analytic lift is equivariant by uniqueness. Consequently the forgetful
functor preserves pullbacks for every cospan, proved by checking it on this
limiting cone.

Pull a jointly surjective family back along a site arrow. For each point of
the new target, choose a point of a covering object above its image in the
original target. The analytic pullback over an étale leg lifts this matching
pair of points, which proves joint surjectivity of the new family. This
verifies stability under base change. Isomorphisms and compositions of
covering families are already covered by the jointly surjective precoverage
of underlying points.

The field is complete and ultrametric, and the space and atlas-index
universes agree. The group and field universes are independent of the space
universe.

## Original sources

- V. G. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
  unfinished manuscript (1995–1996), §1.2, printed/PDF p. 3, defines the
  pretopology by the covering families of underlying analytic spaces.
  Literature ID `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
  folder SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`,
  member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  member SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
- V. G. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*,
  Publ. Math. IHÉS 78 (1993), §4.1, printed p. 82 (PDF p. 79), defines the
  jointly surjective analytic étale pretopology. Proposition 1.4.1, printed
  pp. 29–30 (PDF pp. 26–27), gives its fibre-product geometry. Literature ID
  `berkovich-1993-etale-cohomology`, SHA-256
  `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
