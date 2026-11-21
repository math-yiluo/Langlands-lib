# Ordinary local Haar pushforwards for Weyl integration

`OrdinaryWeylHaarLocalPushforwardsStatement` specifies the local measure
input to the ordinary Weyl formula over a nonarchimedean local field, in
any rank. It takes an ambient Haar measure, a right invariant Haar measure
on the given `WeylTorus`, and a left quotient measure that is compatible
with these Haar measures. On the product of the quotient and the regular
torus, weight the product measure by the absolute Weyl discriminant of the
torus point. The measure on the regular torus is the pullback of torus Haar
measure under the inclusion of the regular point subtype.

At every point of the product the statement asks for an open neighborhood
on which the ordinary Weyl map is an open embedding. The pushforward of
the weighted measure restricted to that neighborhood is ambient Haar
measure restricted to the image. This is the local change-of-variables
input to the proved measure and integral decompositions. The Weyl group
factor comes from the global fiber count, after applying the local identities.

The statement is an internal form of the local calculation underlying
Henniart–Lemaire (2011), II.2.10, ordinary formula (2). The source uses the
same discriminant and compatible quotient normalization in the integral
formula. The local pushforwards remain a proof obligation.
