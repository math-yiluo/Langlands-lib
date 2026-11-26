# Semistandard compact pictures at one specified Iwasawa compact

`CompactData.atMinimalIwasawa` constructs the compact picture at every
intrinsic semistandard index with the same prescribed compact open
subgroup \(K\). It uses \(G(F)=P_0(F)K\) for the minimal standard
parabolic. The published cocharacter coverage realizes the literal
parabolic of each index, and the dynamic Iwasawa theorem gives
\(G(F)=P(F)K\) at that subgroup. `projectionContinuity` gives continuity
of the actual Levi projection. `atMinimalIwasawa_compact` identifies
the resulting compact with the input \(K\).

Waldspurger uses one such \(K\) in I.1, printed p. 240, and takes the
compact picture by restriction to that subgroup in IV.1, printed
pp. 276–277. The construction implements this choice with the actual
rational-point groups and the published minimal-to-dynamic product
comparison.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
