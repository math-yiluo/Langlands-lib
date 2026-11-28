# Global realization of a local division algebra at two places

`TwoPlaceDivisionGlobalizationStatement` starts with a nonarchimedean
local field \(F\) of characteristic zero and a finite-dimensional central
division algebra \(D/F\) of dimension \(n^2\) with its module topology.
It gives a totally complex number field \(K\), a central division
algebra \(A/K\) of dimension \(n^2\), and three distinct finite places
\(v,w,r\) of \(K\).

The completions of \(A\) at \(v\) and \(w\) are division algebras. At every
other finite place the statement supplies a size-\(n\) matrix chart over
the completed field. It also supplies a size-\(n\) matrix chart over the
infinite adele ring. The ring isomorphisms \(K_v \simeq F\) and
\(K_v\otimes_K A \simeq D\) are continuous in both directions and commute
with the two scalar embeddings. The tensor product at \(v\) carries its
module topology over \(K_v\). The number field and its central simple
algebra have carriers in `Type`. The universe of \(F\) and \(D\) is free.
The statement includes \(n=1\), when the degree-one algebras at the
chosen places are fields.

## Mathematical origin

This is the arithmetic setting for Deligne, Kazhdan and Vignéras,
*Représentations des algèbres centrales simples p-adiques*,
§B.1.a, §B.1.f–h (printed pp. 78, 81–82). The comparison uses a set
of finite division places and a separate split finite place for the
supercuspidal factor. The one-place formula is obtained from the formula
over the division places. The retained source is
`bdkv-1984-representations-local-field`, SHA-256
`c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3`.

The two-place realization is derived by choosing a totally complex
number field with completion \(F\) and prescribing opposite Brauer
invariants at \(v\) and \(w\), with zero invariant elsewhere. The
invariant of \(D\) has order \(n\). The number field Brauer profile
realization and the degree and period criterion give a division algebra
with the stated completions. At the first place, classification by the
local Brauer invariant and uniqueness of the division representative
identify the completed algebra with \(D\). At the infinite places the
completions are complex and every central simple algebra splits.
