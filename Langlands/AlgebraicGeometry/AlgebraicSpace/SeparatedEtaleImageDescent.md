# Effective descent of compact separated etale images

This internal adaptation of `EtaleLocalImageDescent` implements the descent
premise of `SeparatedEtaleImageInduction` using the separated etale saturation
geometry. Its only sheaf separation input is a closed diagonal; the chart
composite to the affine base is etale. No monomorphism to that base is required.

The sheafified chart image is open, hence a sheaf. A supplied compact represented
saturation has a separated etale map to the affine base. Zariski's main theorem
makes this compact scheme quasi-affine. The published quasi-affine descent
theorem then represents the image. The projection from the saturation descends
to an etale surjective scheme morphism, so compactness passes to the new
representative. Combined with finite-field-fibre induction, this yields a compact
scheme representative for each affine chart image after affine etale base
change. The final definition chooses such a representative and its isomorphism.
