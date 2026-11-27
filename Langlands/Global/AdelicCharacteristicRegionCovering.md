# Exhaustive characteristic truncation data

For the characteristic regions of Delorme, *On the spectral theorem of
Langlands* (2023), §7, pp. 22–23, the lower simple-root cutoff is fixed and
the upper fundamental-weight cutoff varies. The union over its upper
parameters covers the norm-one rational quotient for suitable fixed Siegel
data satisfying (7.1).

`height_mem_realCorootSpan_of_normOne` expresses the norm-one condition in
cocharacter coordinates. Iwasawa writes a norm-one point as a minimal
parabolic point times a compact point. The compact point has zero character
logarithm, so the parabolic point is also norm-one in the ambient group.
The minimal height annihilates the restricted ambient characters. The
annihilator of their real span is the relative coroot space.

`characteristicRegion_covering` starts from Arthur's Siegel covering and
adjoins compact rational covering factors in the minimal Levi and unipotent
radical. After removing the rational left factor of a Siegel representative,
the combined Levi and positive torus term remains in the ambient norm-one
group. Its height is the height of the positive torus factor. That height
satisfies the fixed lower root inequalities, and choosing it as the upper
parameter makes every upper weight of the difference zero. This supplies a
characteristic truncation parameter for each quotient class.
