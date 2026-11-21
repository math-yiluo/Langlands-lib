# Standard-Levi packet geometry in relative semisimple rank zero

`RankZero.HasPacketStructureAtNormKernel` records compactness of the actual common norm kernel, a simultaneous standard basis there, and the literal Cartan covers of every standard Levi. `RankZero.packetStructure_of_rankZero` proves these properties over a nonarchimedean local field for a connected reductive group with a maximal split torus of relative root rank zero, using the given generic cocharacter.

The relative root span is zero, and the split character lattice injects into its rationalization. Hence the relative root set is empty and the maximal split torus is central. Central-quotient reductivity and compactness of anisotropic rational points then give compactness of the common norm kernel, which is open by the norm-kernel topology theorem.

Every standard Levi is the whole point group and both radicals are trivial. The usual compact-open normal basis has the required Iwahori products and weak chamber contraction, so the published simultaneous basis reduction applies. For the Cartan covers, `fullLatticeRepresentative` supplies an actual finite lattice transversal and a valuation section of products of its representatives with central uniformizer powers. The residual point lies in the norm kernel. Every uniformizer power belongs to each relevant closed chamber because the simple-root indices are empty.

This derived geometry gives the base case for the rank induction in the source-normalized packet proof.
