# Ordinary incident roots in an upper unramified reductive quotient

This internal adapter composes `ApartmentIncidentRootDepth` with
`UnramifiedIncidentRootSurvival`. It works over the actual inertia fixed field
of a nonarchimedean local field in every universe. The model at the supplied
apartment point, its exact neutral integral-point equality, an integral split
torus, and a reductive special-fibre quotient are inputs. The proposition
`UnramifiedRootPositiveReductionStatement` remains an explicit hypothesis.

`exists_unramified_quotient_root_of_incidentAffineRoot` starts from an ordinary
affine root vanishing at the modeled point. The ordinary-root definition
supplies an actual relative root with that derivative and an actual point
outside strict depth times the full doubled-root group. At the modeled point
its depth is zero. The depth-boundary survival theorem shows that the canonical
specialization of this same character belongs to the actual quotient roots.

`unramified_quotient_root_of_incidentAffineRoot` takes a prescribed relative
root and the exact derivative equality. Injectivity of `rootForm` for the
maximal split apartment torus identifies it with the root in the preceding
existence theorem. Its conclusion therefore concerns the specialization of the
prescribed character.

`unramified_quotient_root_of_facet_incidentAffineRoot` allows the model point to
be any point of the full sign facet through the point of incidence. The
definition of the facet forces the affine root to vanish at the model point,
so the same prescribed-root conclusion applies. The exact model equality is
still required at that model point; the lemma does not construct models along
the facet.

`unramifiedIncidentQuotientRoot` packages the actual quotient root for the
incident-root hypothesis used by the coefficient-fixed direction construction.
Its character is definitionally the canonical specialization of the original
root. There is no replacement of that character by a multiple or a root with
merely proportional real derivative.

The provenance is the two imported supporting constructions and the published
split-torus root-form injectivity and sign-facet definition. This adapter
introduces no additional literature assertion. It proves no nonzero restriction
to a smaller torus, supplies no lower-field building, and does not by itself
prove the special-apartment chamber statement.
