# Gluing relative unipotent radicals on etale covers

This internal construction combines closed subgroup cover descent, smoothness
descent, and relative radical transport. It imposes no condition on the base
scheme or universe; the ambient group is affine over it. It derives no new
theorem from external literature.

`CoverDescent.isNormal_subgroup` proves normality of the explicit descended
subgroup on every relative test scheme. Restriction and the base-change point
equivalence preserve conjugation, so normality follows directly from each
local subgroup functor.

`IsRelativeUnipotentRadical.geometricFiber_of_baseChange_at` reflects the
geometric radical condition at the image of a single point under any base
map, assuming the original inclusion is closed. An embedding of the chosen
old algebraic closure into the new one compares the actual geometric fibre
inclusions through the natural pullback square. Field-radical reflection
gives the original geometric fibre condition. No flatness or surjectivity
of this single map is needed.

`RelativeLevi.radicalRepresentativeEtale` takes relative radicals on an
arbitrary etale covering family whose all-test subgroup functors match.
Effective closed subgroup descent supplies a global representative and
the exact local range equalities. Transfer between equal closed
representatives gives full local radical certificates for its pullbacks.
Its smoothness descends by `smooth_of_etaleCover`; normality follows by the
explicit all-test argument above. Every base point has a point above it in
the cover, so pointwise reflection proves its geometric fibre radical
condition. The returned actual closed representative retains the full
relative radical certificate and represents precisely the descended
subgroup functor.

This is a conditional gluing construction: the matching local radicals
are inputs. It does not yet construct them from a relative parabolic
subgroup.
