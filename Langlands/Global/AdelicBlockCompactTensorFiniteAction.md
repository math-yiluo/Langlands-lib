# Finite translation of scalar sections built from compact tensors

`finiteTensorSectionIntertwiner` uses finite evaluations defined on the full finite adelic group. They must intertwine finite right translation and satisfy normalized left parabolic covariance after pairing with an infinite coefficient. The underlying section map also uses the compact parabolic covariance of the paired evaluations.

At a compact point, factor its right-translated finite coordinate into a finite parabolic element and a finite integral element by Iwasawa decomposition. The infinite compact coordinate stays fixed. `normalizedSlice_rightTranslate` expresses the resulting scalar slice using the finite parabolic half character and the translated Levi point. The assumed finite evaluation identities give exactly this value on pure source tensors. Tensor extensionality and the compact picture give the full finite intertwiner.

If the finite factor representation is smooth, `finiteSmoothTensorSectionIntertwiner` maps into the carrier with a common open finite stabilizer. It uses smoothness of the tensor with the trivial finite action on the infinite factor and the smooth-part lift.

This is an internal comparison with the actual action on realized scalar sections. Getz and Hahn (2024), §8.1, pp. 213–214 (PDF 226–227), describe normalized covariance and right translation in local induction. Section 10.1, pp. 270–271 (PDF 282–283), gives the scalar compact model used here.
