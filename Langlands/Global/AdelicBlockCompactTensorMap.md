# Tensor evaluations in the actual adelic compact model

`compactTensorValue` evaluates the finite and infinite tensor factors at the corresponding coordinates of an actual standard compact element. A supplied linear map sends the resulting coefficient tensor to the scalar Levi submodule. On a pure tensor, the value is that linear map applied to the tensor of the two evaluations.

`compactTensorSectionMap` assumes compact parabolic covariance of these scalar values on all pure tensors. Comparing linear maps extends the covariance to arbitrary tensors. The half character on the compact parabolic intersection is one, so this is the normalized scalar covariance used by `CompactSections`. The inverse of `compactPictureEquiv` extends the compact values to scalar sections on the whole adelic group. Their normalized compact slices equal the supplied tensor evaluations for every compact point and every Levi point.

This is an internal construction for the scalar compact picture. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), describe the adelic parabolic and compact factors and the associated scalar Levi slices.
