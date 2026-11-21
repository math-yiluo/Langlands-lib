# The exchange-involutive order action on a split p-divisible group

`PDivisibleGroup.splitOrderAction` takes an order action on a p-divisible
group and the finite Cartier exactness theorem. The ordinary factor acts
on the primal tower. The opposite factor acts on the dual tower by the
Cartier dual morphisms. The action is a ring homomorphism into the
endomorphism ring of the actual product tower.

`Hom.dual` exchanges the two transition arrows and dualizes the maps at
each finite level. It is additive and reverses composition. `Hom.prodMap`
constructs the actual componentwise product of morphisms. These give the
ring homomorphisms used in the action.

`splitOrderAction_adjoint` verifies that the adjoint action for the
principal polarization is given by exchanging the ordinary and opposite
order factors. The proof uses the adjointness of each map and its finite
Cartier dual for evaluation. This is the action and polarization on the
split product of Rapoport–Zink, *Period Spaces for p-divisible Groups*
(1996), §6.43, printed p. 309 (PDF p. 321), in the paragraphs before
(6.17) and Lemma 6.44.
