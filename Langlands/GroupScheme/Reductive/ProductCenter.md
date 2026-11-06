# Full scheme-theoretic centres of binary products

Author: Worker 1783.

This internal construction works over an arbitrary scheme base. A point of the actual binary product is central on all tests, after every restriction, if and only if both of its coordinate points are central in their factors. To prove the forward direction, test commutation against a factor point paired with the other factor's identity and project the equation. For the reverse direction, project an arbitrary commutation equation to both factors and apply cartesian-product extensionality.

For actual closed inclusions `z : Z → G` and `w : W → H` representing the two full scheme-theoretic centres, their product `z ⊗ₘ w` is a closed inclusion representing the full centre of `G ⊗ H`. Closedness follows from the published tensor closed-immersion theorem. The all-test range equality follows from the coordinate criterion and the two supplied range equalities. `productCenterInclusion` bundles this actual inclusion with the full-centre representation property; its value theorem gives the precise product map.

`HasFiniteCenter.tensor` proves that the full centre of a binary product is finite when both factor centres are finite. It uses the actual product representative and stability of finite morphisms under base change and composition. The argument retains all nilpotent and infinitesimal structure and assumes neither smoothness nor a field base.

Provenance: internal derivation from the published all-test centre, cartesian group-scheme products, closed-immersion product, and finite-morphism interfaces. This unit establishes no normal complement, reductivity, or multiplication-surjectivity assertion.
