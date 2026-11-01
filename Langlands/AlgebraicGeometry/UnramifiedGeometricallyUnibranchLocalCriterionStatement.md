# A local criterion for etaleness over a geometrically unibranch domain

Author: Worker 208.

`Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionStatement.{u,v,w}`
is a proposition about actual commutative rings and their actual localizations.
The universes of the base ring `R`, source algebra `S` and chosen base
localization `Rp` are independent. Both `R` and `S` are domains. The
`R`-algebra `S` is of finite type and formally unramified, and its canonical
algebra map is injective. For any prime ideal `q` of `S`, let `Rp` be any
local domain with an `R`-algebra structure exhibiting it as the localization
of `R` at the contracted prime `q.under R`. If `Rp` satisfies the existing
`GeometricallyUnibranchDomain` predicate, the proposition concludes that
some `g : S` outside `q` has `Algebra.Etale R (Localization.Away g)`.
This module defines that proposition without proving it or supplying a witness.

The geometric-unibranch condition is the unchanged predicate imported from
`Picard.GeometricallyUnibranchDomain`: the actual integral closure of `Rp`
in its fraction ring is local, the canonical normalization map is local,
and its induced residue-field extension is purely inseparable. The conclusion
uses Mathlib's etale algebra predicate, including finite presentation, on
the actual principal localization of `S`. It does not assert finite
presentation of an arbitrary prime localization.

The source is the Stacks Project, Lemma 15.109.2, stable tag
[0GSC](https://stacks.math.columbia.edu/tag/0GSC), in the retained source
`stacks-dominant-unramified-etale-2026-11-01`, folder SHA-256
`1216511f5e584381bec8be680f09519c8133ff0ea406fc89ca7e275a68f4a103`,
file `0GSC.html`, assumptions and conclusion. The original proof and empty
comment section were read; no matching project errata note was found.

The provenance is derived. In the source, `R` is a domain, unramifiedness
is required only at `q`, and the localized map `R_p → S_q` is assumed
injective. Here finite type and formal unramifiedness give unramifiedness
at every prime. The domain assumption on `S` and injectivity of `R → S`
imply injectivity of `R_p → S_q`: a fraction mapping to zero has numerator
annihilated after localization; the denominator-clearing element is outside
`q`, hence nonzero in the domain `S`, so the numerator vanishes and then
vanishes in `R`. The arbitrary localization model `Rp` expresses the same
base local ring through its localization universal property. This permits
actual scheme stalks as inputs. These observations explain the specialization;
they are not implemented proofs in this statement module.

No birationality, triviality of the generic extension, noetherianity,
separatedness or flatness assumption is added. This is a supporting local
algebra interface for the dominant unramified scheme criterion. Its proof,
the globalization to actual schemes, and the final exact published scheme
statement remain obligations.
