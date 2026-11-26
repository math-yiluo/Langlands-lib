# Assembly of the uniform algebraic Hecke avatar

`Langlands.GaloisRepresentation.algebraicHeckeAvatarAssembly` proves
`AlgebraicHeckeAvatarAssemblyStatement` from the supplied common finite part,
idele correction, finite geometric Artin lifting, and congruence limit. The
proof uses the integral infinity type of the algebraic CM Hecke character,
which allows nonzero weight.

The finite part supplies one embedded coefficient field \(L\), a lift
\(\varphi\) of the finite idele character, and its conductor support \(S\).
Choose a uniformizer \(\pi_v\) at each finite base place and define \(a_v\)
by evaluating \(\varphi\) on the corresponding one-place finite idele.
The complex embedding sends \(a_v\) to the value of the local Hecke
character at \(\pi_v\).

At a coefficient place \(\lambda\) of residue characteristic \(p\), enlarge
\(S\) by the places of residue characteristic \(p\). Their prime ideals
contain \(p\), so `finite_natCast_mem_asIdeal` gives finiteness. Outside the
enlarged set the correction agrees with the embedded finite part. On local
integral units the complex Hecke character is trivial there. Injectivity of
the complex coefficient embedding and of the inclusion of completed integer
units gives triviality of the integral correction on the same units.
Therefore each congruence reduction satisfies the finite lifting hypothesis.
The supplied limit gives a continuous integral Galois character with the
geometric comparison outside the enlarged set.

Compose the integral character with the inclusion into \(L_\lambda^\times\).
It kills inertia for \(v\notin S\) of residue characteristic different from
that of \(\lambda\). At each such \(v\) the limit comparison sends every
geometric Frobenius lift to the corrected value at \(\pi_v\), which is the
image of \(a_v\) in \(L_\lambda\). This yields the family with the common
support \(S\) and the common values \(a_v\).

The idelic correction and the common good-place values come from Serre,
*Abelian l-Adic Representations and Elliptic Curves*, Chapter II
§§2.3, 2.5 and 2.7, pp. II-10–II-12, II-18–II-20 and II-23–II-24
(`serre-abelian-l-adic-1989`, SHA-256
`971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
The Lean proof obtains the comparison through the finite congruence lifts
and their supplied limit, with the geometric convention of
`FiniteGeometricArtinLifting`.
