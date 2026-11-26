# Tensor powers of kernel translation comparisons

`pullbackPowerMap` conjugates the tensor power of a module map by `pullbackTensorPowIso`, expressing the result as a map between pullbacks of the tensor power. It preserves composition, takes a scalar multiple by `r` to the scalar multiple by `r^n`, and commutes with further pullback by `transport`.

The scalar formula is proved first for the tensor of two sheaf maps. The sheafification adjunction reduces the equality to simple tensors on each open, where the two scalars multiply. Induction gives the formula for tensor powers. The transport formula uses the published composition and naturality laws for `pullbackTensorPowIso`.

These identities implement the tensor-power step in the theta-group formula of Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary version of 8 February 2012, (8.6)(ii) and (iv). The source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, printed p. 115, PDF p. 119.
