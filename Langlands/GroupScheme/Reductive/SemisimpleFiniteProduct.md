# Semisimplicity of finite products

Worker 632.

This internal helper constructs `semisimplePi`, the actual finite categorical
product bundled with its semisimplicity witness, and proves that the product of
semisimple field group schemes is semisimple. The underlying group of the
bundled constructor is exactly the original categorical product. It works over every field and
includes the empty product.

The implemented proof promotes the existing binary product theorem
`DirectProduct.isSemisimple_tensor` and the semisimplicity of the actual trivial
group to closure under finite categorical products, using Mathlib's object
property closure framework. The full scheme-theoretic centre stays finite by
the binary theorem; no reduced-centre or rational-point substitute is used.
This is an auxiliary step in the component decomposition motivating Conrad's
Proposition 6.4.4 and Remark 6.4.5.
