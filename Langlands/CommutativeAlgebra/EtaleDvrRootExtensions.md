# Local etale DVR extensions with prescribed residue roots

Internal derived support for strict Henselian DVR extensions.

Given a monic polynomial over a domain DVR and a simple root at a field point
whose kernel is the maximal ideal, the construction forms the standard etale
algebra that inverts the derivative and localizes at the kernel of that point.
The resulting ring is a local, flat, essentially finite type, formally
unramified algebra, hence a domain DVR by `EtaleDvrExtensions`. Its distinguished
root maps to the prescribed field element.

The embedding lemma passes to fraction fields. Formal unramifiedness and
essential finite type persist under localization and enlargement of the base
to its fraction field. The resulting extension of fields is finite by
Mathlib's unramified free-algebra theorem. An algebraic extension of a field
embeds in any algebraically closed overfield; restricting this embedding gives
an injective algebra map from the original domain extension.

These are internal constructions from Mathlib's standard etale, localization,
and algebraically closed field APIs and the companion local DVR lemmas.
They do not assert the strict Henselization universal property.
