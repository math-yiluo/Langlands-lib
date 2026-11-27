# Exhaustion by characteristic truncation along a dominant ray

This module uses the actual `characteristicRegion` on the norm-one
rational quotient of a connected reductive group. Fix the minimal-parabolic
Iwasawa compact, the compact Siegel factors and the lower basepoint
\(T_0\). The upper cutoffs are the values \(\varpi_\alpha(T)\) of the
fundamental weights at the truncation parameter. Raising all of these
values preserves the defining inequalities and enlarges the region.

Each weight is positive at a vector \(v\) on which all simple relative roots
are positive. The proof uses `ArthurCombinatorics.weightCoordinate_pos` on
the actual coroot span, where the inverse Cartan block has nonnegative
entries and strictly positive diagonal entries. Projecting the defining
cocharacter onto that span has the same simple-root evaluations. This
supplies a direction in the relative space, with vacuous inequalities when
the simple set is empty.

Suppose every quotient class lies in some region for the fixed compact data
and basepoint. Along \(T=r v\) all upper cutoffs grow monotonically. For any
class, the finitely many cutoffs of a region containing it are eventually
bounded by those of \(r v\). Thus the regions along the ray increase and
contain each class for all sufficiently large \(r\).

`characteristicIntegralExhaustion` proves `CharacteristicIntegralExhaustionStatement`.
For measurable regions along the ray and any complex integrable function on
the norm-one rational quotient, the integral over the region converges to
the full integral. The proof uses the monotone-exhaustion theorem for set
integrals with the fixed `normOneRationalQuotientHaarMeasure`. Coverage,
measurability and integrability are inputs. In the packet application the
function is the product of a packet and the conjugate of a tested form.

The chamber and characteristic region are from Delorme, *On the spectral
theorem of Langlands*, Advances in Mathematics 426 (2023), 109107, §7,
pp. 22–23. The use of exhaustion for integrable packet pairings is in the
proof of Lemma 7.11, p. 35. The registered PDF in
`delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
