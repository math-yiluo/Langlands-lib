# Algebra maps out of a presentation

To compare two algebra maps out of `S`, it suffices to compare their values on an algebra generating family. The proof precomposes with the surjection from the polynomial algebra on the generators and uses polynomial extensionality.

For a presentation `P`, `P.lift x hx` constructs the map sending each generator to its prescribed value in a commutative target. The hypothesis says that evaluating each defining relation gives zero. Those relations span the kernel of the presentation map, so polynomial evaluation descends through the surjection. The lemma `P.lift_val` computes the resulting map on each generator.
