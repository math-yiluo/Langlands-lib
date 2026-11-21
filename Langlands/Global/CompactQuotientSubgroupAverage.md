# Averaging over a compact subgroup quotient

The transitivity of constant terms is used in Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.3.4, p. 45: the cuspidal components of a form and of its constant term along a larger parabolic agree at every smaller standard parabolic. This module proves the measure step of that argument for abstract groups. Its Riesz representation proof is an internal derivation on the Library's actual left homogeneous quotients. The adelic group and lattice comparisons are not part of this module.

## The average

Let \(\Gamma \le H\) and \(\Delta \le N\) be subgroups and let \(j:N\to H\) be a continuous homomorphism taking \(\Delta\) into \(\Gamma\). `subgroupFiberEval` sends \(q=[n]\) in \(\Delta\backslash N\) to \(f([j(n)x])\) for fixed \(x\in H\). This is well-defined because \(j(\Delta)\subseteq\Gamma\). When \(f\) is continuous it is jointly continuous in \(x\) and \(q\), by the open quotient map on the second factor.

We suppose that for each \(\gamma\in\Gamma\) a homeomorphism \(e\) of \(\Delta\backslash N\) preserves the inner measure \(\mu\) and satisfies \([j(n)\gamma]=[j(n')]\) whenever \([n']=e([n])\). For example, `subgroupAverageConjugation` supplies this comparison if an automorphism \(a\) of \(N\) preserves \(\Delta\) and its quotient measure and satisfies \(j(a(n))=\gamma^{-1}j(n)\gamma\). The condition is about the outer lattice \(\Gamma\), not about conjugation by arbitrary elements of \(H\).

`compactSubgroupAverage` is the descended function

\[
(Af)([x])=\int_{\Delta\backslash N} f([j(n)x])\,d\mu([n]).
\]

Changing \(x\) to \(\gamma x\) changes the integration variable by the given measure-preserving homeomorphism. For finite \(\mu\) on the compact inner quotient, joint continuity gives continuity of the parameterized integral, and hence continuity on the outer quotient. The same formula commutes with right translations by associativity. It makes no assertion that either left quotient is a group.

## The integral identity

Assume the quotients are compact, \(H\) is Hausdorff and locally compact, \(\Gamma\) is closed with supplied regular two-sided Haar measure, the measurable structures are Borel, \(\mu\) is a probability, and the outer measure \(\nu\) is a regular right-invariant probability. Then `integral_compactSubgroupAverage` proves

\[
\int_{\Gamma\backslash H} Af\,d\nu = \int_{\Gamma\backslash H} f\,d\nu
\]

for real or complex continuous \(f\) (Lean uses `RCLike`). On real compactly supported continuous functions, the averaging map is positive and linear, by integrability on every compact fiber. The Riesz measure of \(g\mapsto\int Ag\,d\nu\) is regular and has mass one, by testing the constant function \(1\). Its pushforward by any right translation has the same integrals against all real compact tests, by equivariance of \(A\) and right invariance of \(\nu\); extensionality gives right invariance. The existing `exists_pos_smul_eq_of_rightInvariant_quotient` then identifies the two measures up to a scalar, which is one by normalization. Real and imaginary parts commute with both integrals, giving the complex version.

`measurePreserving_quotientAutomorphism_of_probability` uses the same uniqueness of regular right-invariant probability: the pushforward under a lattice-preserving continuous automorphism is regular, has the same mass, and is right invariant since the automorphism intertwines right translations. It can discharge the measure-preservation hypothesis in the conjugation comparison once the group and lattice identities are known.
