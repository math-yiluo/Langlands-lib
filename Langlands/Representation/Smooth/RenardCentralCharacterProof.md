# Central characters and the categorical center

Author: Worker 138. Namespace `Langlands.Renard.Smooth`.

The theorem `centralCharacter` proves exactly `CentralCharacterStatement`, covering the central-character assertion, the Lemma and the categorical-center Remark of Renard III.1.10. Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, printed pp.63–64 / PDF pp.69–70; registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For each element of the supplied central subgroup, its representation operator is an intertwining endomorphism. The III.1.8 proof `sigmaCompactSchur` makes this operator scalar. Evaluation at one fixed nonzero vector proves that these scalars preserve one and multiplication. Evaluation on the inverse shows each scalar is nonzero, so the actual scalar map gives a monoid homomorphism into `ℂˣ`. The construction uses the same elementary scalar-character argument as the published admissible Schur proof, replacing its admissibility input by sigma-compact smooth Schur.

For distinct characters, choose a central element where they differ. Intertwining implies that the difference of their scalar values annihilates every image vector. That scalar is nonzero, so the intertwiner vanishes. This step uses neither smoothness nor irreducibility, in agreement with the statement.

Finally, a component of an endomorphism of the identity functor of the smooth representation category is already an intertwining endomorphism. Applying `sigmaCompactSchur` to that component proves the required scalar action. No further property of the categorical center is required. Both carrier universes remain independent, and no hypothesis is added. The published statement pair and its imports are unchanged.
