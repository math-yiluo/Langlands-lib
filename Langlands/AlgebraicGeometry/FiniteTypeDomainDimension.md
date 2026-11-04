# Dimension of a finite-type domain over a field

This is a derived internal comparison for the component-dimension locality
needed in Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The registered
original is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It is not a separately numbered assertion of Conrad.

`finiteTypeDomainDimension k A` is the natural number obtained from the
transcendence degree of the actual k-algebra A. Without finite type,
Cardinal.toNat is only an auxiliary construction. For finite-type
commutative domains over a field, the comparison theorem proves that
its natural-number cast equals the actual ring Krull dimension.

The implemented proof uses Noether normalization to embed a polynomial
ring in finitely many variables into A with A finite over it. Integral
injective maps preserve Krull dimension. Additivity of transcendence
degree, together with algebraicity of the integral extension, computes
the transcendence degree as the number of polynomial variables.

The final comparison treats a compatible tower k → A → B of finite-type
domains over a field. An injective algebraic map A → B gives zero relative
transcendence degree, so additivity identifies the two constructed
dimensions and hence their actual Krull dimensions. The universes of k,
A and B are independent. This comparison concerns domains only; it
also applies when B is the actual principal localization A[1/s], for
any nonzero s. Such a localization is a domain, the structure map from
A is injective and algebraic, and adjoining the inverse of one element
preserves finite type over k. Consequently
`ringKrullDim (Localization.Away s) = ringKrullDim A`.

The nonzero hypothesis is essential: localization at zero is the zero
ring, whose spectrum is empty. No localization-at-a-prime claim is
made; that algebra need not be finite type over k and can have a
different Krull dimension. These are intrinsic comparisons of the
transcendence-degree dimension construction on domains. They do not
yet assert componentwise locality for general schemes, field-extension
invariance for nonaffine schemes, constructibility, or filtered descent.
