# Residue characters of the special tangent representation

Drinfeld's special condition gives one geometric tangent eigenline for each distinct character of the unramified integer subfield. This module derives a way to match those eigenlines across special formal modules over the same residue algebra field. It uses the actual embedded integer ring, its residue field, and the central scalar action on the formal tangent space.

`factorSubfieldCharacter` descends a central-linear character to the residue field. The integral extension is finite étale and local, so its maximal ideal is the extension of the central maximal ideal. The character kills that ideal because the central map into the coefficient field factors through the central residue field.

`tangentSubfieldCharacter` obtains central linearity from the actual structural scalar action. `tangentResidueCharacters` is an equivalence from the tangent decomposition's indices to the residue-field embeddings. The reduction of the characters is injective by their original distinctness. The residue-field degree bounds the number of embeddings by the number of tangent indices, so the injection is surjective. The evaluation lemma recovers the original tangent character on every integral element.

Source for the special condition and dimension is Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3). The residue factorization and indexing argument are derived from that condition and the finite étale structure of the embedded integer ring.
