# Cartier duality of rational tower morphisms

Actual finite Cartier duality preserves addition and the identity. It
therefore preserves multiplication by the integral representative of
any \(p\)-adic scalar at level \(n\), taken modulo \(p^n\). At the tower
level, contravariance and the naturality of the scalar action give
`Hom.dualLinear` on integral morphism groups.

`RationalHom.dualMap` extends this map to the scalar tensor and reverses
composition. `QuasiIsogeny.dual` applies it to the forward and inverse
maps. The resulting quasi-isogeny has the dual of the original target
as its source and the dual of the original source as its target.

In Rapoport–Zink (1996), §6.43, printed p. 309 (PDF p. 321), the
rigidifier for the dual factor is obtained by taking the inverse of the
Cartier dual of the primal rigidifier. The operation defined here gives
that dual on the actual p-divisible groups.
