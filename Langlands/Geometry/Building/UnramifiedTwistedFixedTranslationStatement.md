# Twisted coefficient-fixed translations of a special apartment

This module contains one definition and one proposition. Together they make up
the second of three inputs into which
`UnramifiedTorusUnitFixedApartmentStatement` (Kaletha–Prasad Proposition
9.3.13) is split.

## The split translation directions

`splitTranslationDirections k K iT f` is a real subspace of
`TranslationSpace`. That space is the translation space of the apartment of
the extended torus \(T_K\): the quotient of \(V(T_K) = \mathbb R \otimes
X_*(T_K)\) by `rootAnnihilator`, the common kernel of the relative roots.
The subspace is built in two steps:

1. Take the range of the real scalar extension `cocharacterMapReal`, which
   postcomposes cocharacters of \(S_K\) with the extension of \(f : S \to T\).
2. Map that range to the quotient by the quotient map `mkQ`.

So the subspace is the image of \(V(S_K)\) among the apartment translations.
When \(S\) is a maximal \(F\)-split torus of \(G\), Kaletha–Prasad write the
corresponding space of translations as \(V(S')\), with \(S'\) the maximal
subtorus of \(S\) in the derived group (§9.3, before Proposition 9.3.13, PDF
page 369). The Library's `TranslationSpace` is not identified with \(V(T'_K)\)
here, so the definition uses the quotient image of \(V(S_K)\). The two agree
once the root annihilator is identified with the central directions.

The definition itself takes any `f` and assumes no maximality. Only in the
maximal split setting of the statement below does it play the role of
\(V(S')\). For a non-maximal split subtorus the quotient image can be larger
than \(V(S')\). Take \(G = \mathrm{GL}_2\), \(T\) diagonal and \(S =
\{\operatorname{diag}(t, 1)\}\). Then \(S' = 1\), but the image of \(V(S) =
\mathbb R(1,0)\) modulo the root kernel \(\mathbb R(1,1)\) is nonzero.

## The statement

The setting of `UnramifiedTwistedFixedTranslationStatement` is:

- \(F\) is a nonarchimedean local field, \(K\) is its maximal unramified
  extension `inertiaFixedField F`, and \(G\) is a connected reductive group
  over \(F\).
- \(S\) is a maximal \(F\)-split torus, \(f : S \to T\) factors its inclusion
  through an \(F\)-torus \(T\), and \(T_K\) is maximal \(K\)-split in \(G_K\).

The remaining hypotheses are:

- an element \(h \in G(K)\) that commutes with every point of \(S_K(K)\);
- a family \(n_\sigma\) of normalizer points of \(T_K\) with
  \(n_\sigma = h^{-1}\sigma(h)\) for every \(\sigma \in \operatorname{Aut}(K/F)\);
- a translation \(v\) with
  \(n_\sigma \cdot \sigma(v) = v\) for every \(\sigma\).

Here \(\sigma(h)\) is the coefficient conjugate `rationalConjugate`,
\(\sigma(v)\) is the coefficient action `galoisTranslationAction` on the
translation space, and \(n \cdot (-)\) is the linear normalizer action
`translationAction`.

The conclusion is that \(v\) lies in `splitTranslationDirections`.

## Mathematical content and provenance

This is a derived formulation of the first paragraph of the proof of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition
9.3.13, printed page 338 (PDF page 369). The book is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The
proof states
\(V(T')^{\Gamma} = V(S')\) for a special \(F\)-torus \(T\) containing \(S\),
because \(S'\) is the maximal \(F\)-split torus in \(T'\).

Here the torus is \(hT_Kh^{-1}\), presented through \(T_K\):

- Because \(n_\sigma\) normalizes \(T_K\), the torus \(hT_Kh^{-1}\) is
  \(\operatorname{Aut}(K/F)\)-stable. It contains \(S_K\) because \(h\)
  commutes with \(S\).
- Conjugation by \(h\) carries the twisted action
  \(v \mapsto n_\sigma \cdot \sigma(v)\) on the cocharacters of \(T_K\) to
  the Galois action on the cocharacters of \(hT_Kh^{-1}\).
- It fixes the cocharacters of \(S_K\).

The statement therefore says that the twisted-fixed directions are exactly
the directions of the maximal split subtorus \(S\), read in the quotient
`TranslationSpace`.

The authors' *Corrections and additions*, version of 1 November 2024,
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
pages 39–40, must accompany Section 9.3. They leave this paragraph of the
proof of 9.3.13 unchanged and delete only its last paragraph.

No proof is provided here; the Lean declaration is a proposition definition.
