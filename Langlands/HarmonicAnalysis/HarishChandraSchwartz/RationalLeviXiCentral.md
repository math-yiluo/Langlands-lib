# Central invariance of the actual Levi Xi weight

This supporting module supplies the actual Xi invariance used in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra*
(2003), proof of Lemma VI.2.3, printed p.301: translating a point by a power of
a point in the split component of the Levi does not change its Levi Xi value.
The original source is registered as `waldspurger-2003-plancherel`.

`rationalMinimalComponentHom` is the homomorphism from the specified `A(F)` to
the actual minimal Levi `M₀(F)` obtained from the given torus map `q : A → S`.
Its inclusion into `M_J(F)` is exactly the published `standardComponentHom`,
and its `H₀` value is the published `rationalComponentH0`.

The proof first treats a point central in `M_J(F)` and lying in `P₀(F)`.
`standardLeviMinimalModulus_eq_one_of_commute` makes its minimal Levi modulus
one. The published `xi_mul_left_of_eq_one` then gives invariance, using
`standardLeviMinimalModulusOf_eq_one` on the compact subgroup. A point of a
compatible split component is central by `standardComponentHom_commute` and
lies in `M₀(F)`, so this proves right translation invariance on `M_J(F)` and
on the actual minimal Levi through `minimalLeviInclusion`.

The compact subgroup is open and compact, the displayed Iwasawa pair is the
actual one, and `J` is contained in the simple relative roots. No exponent,
constant-term, or coefficient estimate is assumed. The module is derived
infrastructure for Task 7559, not a proof of the uniform positive-decay target.
The target and its imports are unchanged.
